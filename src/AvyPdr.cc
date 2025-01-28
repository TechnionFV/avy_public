#include <fstream>
#include <string>

#include "boost/noncopyable.hpp"
#include "boost/program_options.hpp"
#include "boost/scoped_ptr.hpp"

#include "avy/Util/AvyTribool.h"

#include "aig/gia/giaAig.h"

namespace po = boost::program_options;

#include "AigUtils.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "Pdr.h"
#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"

using namespace avy;
using namespace avy::abc;

namespace ABC_NAMESPACE {
extern Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
} // namespace ABC_NAMESPACE

namespace avy {

class AvyPdr : boost::noncopyable {
  std::string m_sFName;

public:
  AvyPdr(std::string fname) : m_sFName(fname) { Abc_Start(); }
  ~AvyPdr() { Abc_Stop(); }

  tribool run() {
    AVY_MEASURE_FN;
    Stats::set("Result", "UNKNOWN");
    VERBOSE(1, Stats::PrintBrunch(vout()););

    std::string &fname = m_sFName;
    Abc_Frame_t *pAbc = Abc_FrameGetGlobalFrame();
    VERBOSE(2, vout() << "\tReading AIG from '" << fname << "'\n";);
    std::string cmd = "&r " + fname;
    Cmd_CommandExecute(pAbc, cmd.c_str());
    Cmd_CommandExecute(pAbc, "&put");

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    Pdr pdr(Abc_NtkToDar(pNtk, 0, 1));
    VERBOSE(2, pdr.setVerbose(true););
    tribool res = pdr.solve();

    Stats::uset("Frames", pdr.maxFrames());
    VERBOSE(1, vout() << "Result: " << std::boolalpha << res << "\n");
    if (!res)
      Stats::set("Result", "SAT");
    else if (res)
      Stats::set("Result", "UNSAT");

    if (!gParams.cexFileName.empty()) {

      std::ostream *pOut;
      boost::scoped_ptr<std::ofstream> pFout;

      if (gParams.cexFileName == "-")
        pOut = &outs();
      else {
        pFout.reset(
            new std::ofstream(gParams.cexFileName.c_str(), std::ofstream::out));
        pOut = pFout.get();
      }
      std::ostream &out = *pOut;

      if (!res) {
        VERBOSE(1, vout() << "Generating counterexample: "
                          << gParams.cexFileName << "\n";);

        out << "1\n"
            << "b0\n";

        Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
        Abc_Cex_t *pCex = pdr.get()->pAig->pSeqModel;

        Abc_Obj_t *pObj;
        int i;
        Abc_NtkForEachLatch(pNtk, pObj, i) out
            << (Abc_LatchIsInit0(pObj) ? "0" : "1");

        for (i = pCex->nRegs; i < pCex->nBits; ++i) {
          if ((i - pCex->nRegs) % pCex->nPis == 0)
            out << '\n';
          out << (Abc_InfoHasBit(pCex->pData, i) ? "1" : "0");
        }
        out << "\n.\n";
      } else if (res)
        out << "0\nb0\n.\n";
    }

    if (!gParams.certificate.empty()) {
        Aig_Man_t *pAig = Aig_ManStart(10000);
        Aig_Man_t *pCirc = pdr.get()->pAig;

        unsigned numRegs = Aig_ManRegNum(pCirc);
        unsigned numPIs = Aig_ManCiNum(pCirc) - numRegs;
        for(unsigned i=0; i <  numRegs; i++)
        {
            Aig_ObjCreateCi(pAig);
        }

        Vec_Ptr_t *pInvar = Vec_PtrAlloc(16);;
        pdr.getInvarCubes(pInvar);

        Pdr_Set_t *pCube;
        unsigned j;
        Aig_Obj_t *pInv = Aig_ManConst1(pAig);
        Vec_PtrForEachEntry(Pdr_Set_t *, pInvar, pCube, j) {
            Aig_Obj_t *pCls = Aig_ManConst0(pAig);
            for (unsigned i = 0; i < pCube->nLits; i++ ) {
                if (pCube->Lits[i] == -1)
                    continue;
                AVY_ASSERT(lit_var(pCube->Lits[i]) < numRegs);
                Aig_Obj_t *pObj = Aig_ManCi(pAig, lit_var(pCube->Lits[i]));
                pCls = Aig_Or(pAig, pCls, (lit_sign(pCube->Lits[i])) ? pObj : Aig_Not(pObj));
            }

            pInv = Aig_And(pAig, pInv, pCls);
        }

        Aig_ObjCreateCo(pAig, Aig_Not(pInv));

        Aig_Man_t *pNew = Aig_ManReplacePo(pCirc, pAig, 0);

        Gia_Man_t *p = Gia_ManFromAigSimple(pNew);
        Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();
        Abc_FrameUpdateGia(pFrame, p);
        Cmd_CommandExecute(pFrame, std::string("&put; write_aiger " + gParams.certificate).c_str());

        Vec_PtrClear(pInvar);
        Vec_PtrFree(pInvar);

        Aig_ManStop(pAig);

    }

    VERBOSE(1, Stats::PrintBrunch(vout()););
    return res;
  }
};
} // namespace avy

static std::string parseCmdLine(int argc, char **argv) {
  po::options_description generic("Options");
  generic.add_options()("help", "print help message")(
      "log,L", po::value<std::vector<std::string>>(), "log levels to enable")(
      "verbose,v", po::value<unsigned>(&gParams.verbosity)->default_value(0),
      "Verbosity level: 0 means silent")(
      "cex", po::value<std::string>(&gParams.cexFileName)->default_value(""),
      "Location to output counter-example")(
          "certificate",
          po::value<std::string>(&gParams.certificate)
                  ->default_value("avy_cert.aig")
                  ->implicit_value("avy_cert.aig"),
          "Provide a file name for avy certificate");

  po::options_description hidden("Hidden options");
  hidden.add_options()("input-file", po::value<std::string>(), "input file");

  po::options_description cmdline;
  cmdline.add(generic).add(hidden);

  po::positional_options_description p;
  p.add("input-file", -1);

  try {
    po::variables_map vm;
    po::store(po::command_line_parser(argc, argv)
                  .options(cmdline)
                  .positional(p)
                  .run(),
              vm);
    po::notify(vm);

    if (vm.count("help")) {
      outs() << generic << "\n";
      std::exit(1);
    }

    if (!vm.count("input-file")) {
      outs() << "Error: No AIG file specified\n";
      std::exit(1);
    }

    if (vm.count("log")) {
      using namespace std;
      vector<string> logs = vm["log"].as<vector<string>>();
      for (vector<string>::iterator it = logs.begin(), end = logs.end();
           it != end; ++it)
        AvyEnableLog(it->c_str());
    }

    gParams.fName = vm["input-file"].as<std::string>();
    return gParams.fName;
  } catch (std::exception &e) {
    outs() << "Error: " << e.what() << "\n";
    std::exit(1);
  }
}

int main(int argc, char **argv) {
  std::string fileName = parseCmdLine(argc, argv);
  gParams.num_extra_frames = 100;
  AvyPdr pdr(fileName);
  tribool res = pdr.run();
  if (res)
    return 0;
  else if (!res)
    return 1;
  else
    return 2;
}
