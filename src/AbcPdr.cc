#include <fstream>
#include <string>

#include "avy/Util/AvyTribool.h"

#include "boost/noncopyable.hpp"
#include "boost/program_options.hpp"
#include "boost/scoped_ptr.hpp"
namespace po = boost::program_options;

#include "AigUtils.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"
#include "aig/gia/giaAig.h"

using namespace avy;
using namespace avy::abc;

namespace ABC_NAMESPACE {
extern Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
extern int Abc_CommandPdr(Abc_Frame_t *pAbc, int argc, char **argv);
} // namespace ABC_NAMESPACE

namespace avy {

class AbcPdr : boost::noncopyable {
  std::string m_sFName;

public:
  AbcPdr(std::string fname) : m_sFName(fname) { Abc_Start(); }
  ~AbcPdr() { Abc_Stop(); }

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

    cmd = "pdr";
    VERBOSE(2, cmd += " -v";);
    cmd += " -z -d -e";

    Stats::resume("run.loop");
    Cmd_CommandExecute(pAbc, cmd.c_str());
    Stats::stop("run.loop");

    int status = Abc_FrameReadProbStatus(pAbc);
    tribool res;
    if (status == 0)
      res = true;
    else if (status == 1)
      res = false;

    int nFrames = Abc_FrameReadBmcFrames(pAbc);
    Stats::uset("Depth", nFrames < 0 ? 0 : nFrames);

    VERBOSE(1, vout() << "Result: " << std::boolalpha << res << "\n");
    if (res)
      Stats::set("Result", "SAT");
    else if (!res)
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

      if (res) {
        VERBOSE(1, vout() << "Generating counterexample: "
                          << gParams.cexFileName << "\n";);

        out << "1\n"
            << "b0\n";

        Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
        Abc_Cex_t *pCex = static_cast<Abc_Cex_t*>(Abc_FrameReadCex(pAbc));

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
      } else if (!res)
        out << "0\nb0\n.\n";
    }

    if (!res && !gParams.certificate.empty()) {
        Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
        Aig_Man_t *pCirc = Abc_NtkToDar(pNtk, 0, 1);
        std::string inv_name = std::string(pCirc->pName) + "_inv.pla";
        cmd = "read " + inv_name + "; strash";
        Cmd_CommandExecute(pAbc, cmd.c_str());
        pNtk = Abc_FrameReadNtk(pAbc);
        Aig_Man_t *pAig = Abc_NtkToDar(pNtk, 0, 1);
        Aig_Man_t *pInv = Aig_ManReplacePo(pCirc, pAig, false);
        Gia_Man_t *pGia = Gia_ManFromAigSimple(pInv);
        Abc_FrameUpdateGia(pAbc, pGia);
        cmd = "&put; write_aiger " + gParams.certificate;
        Cmd_CommandExecute(pAbc, cmd.c_str());
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
  AbcPdr pdr(fileName);
  tribool res = pdr.run();
  if (res)
    return 1;
  else if (!res)
    return 0;
  else
    return 2;
}
