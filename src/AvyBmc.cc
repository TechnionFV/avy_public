#include <fstream>
#include <string>
#include <vector>

#include <avy/Util/AvyTribool.h>

#include "boost/noncopyable.hpp"
#include "boost/program_options.hpp"
#include "boost/scoped_ptr.hpp"
namespace po = boost::program_options;

#include "AigUtils.h"
#include "Glucose.h"
#include "Minisat.h"
#include "ItpGlucose.h"

#include "AigPrint.h"
#include "SafetyVC2.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"
#include "aig/saig/saig.h"

#include "Unroller.h"
#include "simp/SimpSolver.h"
#include "AvyTypes.h" //IntVector

using namespace boost;
using namespace std;
using namespace avy;
using namespace avy::abc;

namespace ABC_NAMESPACE {
extern Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}

static Aig_Man_t *loadAig(std::string fname) {
  Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();

  VERBOSE(2, vout() << "\tReading AIG from '" << fname << "'\n";);
  std::string cmd = "read " + fname;
  Cmd_CommandExecute(pFrame, cmd.c_str());

  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pFrame);

  return Abc_NtkToDar(pNtk, 0, 1);
}

static std::string gCnfFile;
static bool gDoBmc;

namespace avy {
class AvyBmc : boost::noncopyable {
private:
  std::string m_FName;
  bool m_doBmc;
  AigManPtr m_Aig;

  std::string m_CnfFile;

  bool m_bExtend;
  bool m_bRes;

  std::vector<bool> m_lastFrame;

public:
  AvyBmc(std::string fname, bool doBmc, bool extend);
  ~AvyBmc();

  avy::tribool run(unsigned uDepth);

  template <typename Sat>
  avy::tribool bmc(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                     unsigned uDepth);

  template <typename Sat> void printCex(Sat &s, Unroller<Sat> &unroller);
  template <typename Sat> void printCexBv(Sat &s, Unroller<Sat> &unroller);

  void setCnfFile(std::string &cnf) { m_CnfFile = cnf; }

  template <typename Sat> void getInputVals(Sat &s, Unroller<Sat> &unroller, vector<lit> & vals);

};

AvyBmc::AvyBmc(std::string fname, bool doBmc = true, bool extend = false)
    : m_FName(fname), m_doBmc(doBmc), m_bExtend(extend), m_bRes(false) {
  VERBOSE(2, vout() << "Starting ABC\n");
  Abc_Start();
  m_Aig = aigPtr(loadAig(fname));
}

AvyBmc::~AvyBmc() { Abc_Stop(); }

tribool AvyBmc::run(unsigned uDepth) {
  Stats::set("Result", "UNKNOWN");
  VERBOSE(1, Stats::PrintBrunch(outs()););
  avy::tribool res = false;

  SafetyVC2 vc(&*m_Aig, gParams.opt_bmc,gParams.lemmaAbs,nullptr);

  m_bRes = false;
  if (gParams.glucose) {
    Glucose sat(2, gParams.sat_simp);
    Unroller<Glucose> unroller(sat, nullptr, false);
    for (unsigned f = 0; f < uDepth; f++) {
      res = bmc(vc, sat, unroller, f);
      if (res) {
        if (!gParams.bmc_incremental_assignment || f+1 == uDepth) {
          Stats::set("Result", "SAT");
          Stats::uset("Depth", f+1);
          VERBOSE(1, Stats::PrintBrunch(outs()););
          printCex(sat, unroller);
          return res;
        } else {
          Stats::set("Result", "SAT");
          Stats::uset("Depth", f+1);
          VERBOSE(1, Stats::PrintBrunch(outs()););
          vector<lit> vals;
          getInputVals(sat, unroller, vals);
          sat.setHints(vals);
        }
      }
      m_bRes = res;
    }
    if (res) {
      // printCex(sat, unroller);
      return res;
    }
  } else {
    Minisat sat(5000, gParams.sat_simp);
    Unroller<Minisat> unroller(sat, nullptr, false);
    for (unsigned f = uDepth; f <= uDepth; f++) {
      res = bmc(vc, sat, unroller, f);
      if (res) {
        printCex(sat, unroller);
        break;
      }
    }
  }

  VERBOSE(1, Stats::PrintBrunch(outs()););
  return tribool();
}

template <typename Sat>
tribool AvyBmc::bmc(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                    unsigned uDepth) {
  AVY_MEASURE_FN;

  if (!gParams.incr) {
      solver.reset(2);
      unroller.reset(&solver, nullptr);
      vc.reset();
  }
  unroller.resetLastFrame();

  AigManPtr pBad = nullptr;

    if (!gParams.coi) {
        ScoppedStats _s_("bmc_unroll");
        for (unsigned i = unroller.frame(); i <= uDepth; ++i) {
            // -- add Tr logic to unroller and the underlying sat-solver
            vc.addTr(unroller);
            // HG : If there were new lemmas added to previous frames
            // HG : we ignore them non coi plus incr mode
            unroller.newFrame();
        }
    } else {
        ScoppedStats _s_("bmc_unroll");
        if (pBad == nullptr) { pBad = vc.getBad(); }
        // -- assuming that the first output of pBad is the bad output
        vector<int> bad(1, 0);
        IntVector support;
        Aig_GetSupport(&*pBad, bad, support);
        if (unroller.frame() > uDepth) {
            // -- when doing QUIP, the unroller is already unrolled enough
            // -- so just calculate the support at the required frame
            // HG : nFrame is always equal to unroller.frame()-1
            vc.addTrLogicRec(unroller, support, uDepth);
            vc.addCondLogicRec(unroller, uDepth);
        } else {
            for (unsigned i = unroller.frame(); i <= uDepth; ++i) {
                // -- set up frames and unroller
                vc.setupFrame(unroller, false);
                // -- last iteration: add COI of bad
                if (i == uDepth) {
                    vc.addTrLogicRec(unroller, support);
                    vc.addCondLogicRec(unroller);
                }
                unroller.newFrame();
            }
        }
    }

    for (unsigned i=0; i <= uDepth; i++) {
        unroller.setFrozenInputs(i, true);

        if (gParams.incr && gParams.coi) {
            vector<int> vars;
            vc.getUncommitedInFrame(i, vars);
            unroller.setFrozenVars(vars, true);
        }
    }
    // -- freeze current outputs
    unroller.setFrozenOutputs(uDepth, true);

    // -- add constraints for pBad into the last frame
    vc.addBad(unroller, pBad);

  if (m_bExtend && m_bRes) {
    abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(unroller.frame() - 1);

    int j, input;
    Vec_IntForEachEntry(PIs, input, j) {
      if (j == 0)
        continue;
      lit q = toLit(input);
      if (!m_lastFrame[j])
        q = lit_neg(q);
      solver.addClause(&q, &q + 1);
    }
  }

  IntVector assumptions;
  assumptions.push_back(unroller.getBadLit());
  int reset_input = Vec_IntGetEntry(unroller.getPrimaryInputs(0), 0);
  assumptions.push_back(lit_neg(reset_input));
  if (m_CnfFile != "")
    solver.dumpCnf(m_CnfFile, assumptions);

  for (lit Lit : assumptions) {
        solver.markSelector(lit_var(Lit), true);
  }

  tribool res = false;
  if (m_doBmc) {
    vout() << "Assumption is: " << unroller.getBadLit() << "\n";
    ScoppedStats _s_("solve");
    VERBOSE(1, vout() << "Solving " << uDepth << " ...\n" << std::flush;);
    res = solver.solve(assumptions);
      if (gParams.incr && gParams.coi) {
          for (unsigned i = 0; i <= uDepth; i++) {
              vector<int> vars;
              vc.getUncommitedInFrame(i, vars);
              unroller.setFrozenVars(vars, false);
          }
      }
    lit p = lit_neg(assumptions[0]);
    if (!m_bExtend)
      solver.addClause(&p, &p + 1);
    VERBOSE(1, vout() << "Result: " << std::boolalpha << res << "\n");
    if (res)
      Stats::set("Result", "SAT");
    else if (!res)
      Stats::set("Result", "UNSAT");
  }
  if (m_bExtend && res) {
    m_lastFrame.clear();
    for (unsigned x = 0; x <= unroller.frame() - 1; x++) {
      abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(x);
      // abc::Vec_Int_t* currPIs = unroller.getPrimaryInputs (unroller.frame());

      int j, input;

      Vec_IntForEachEntry(PIs, input, j) {
        // -- skipping the first input of the first and last
        // -- frames. It is used for reset and is not part of the
        // -- original circuit.
        if (j == 0 /*&& (i == 0 || i + 1 == unroller.frames ())*/)
          continue;
        // int cinput =  Vec_IntEntry (currPIs, j);
        lit q = toLit(input);
        // lit p = toLit(cinput);
        outs() << (solver.getVarVal(input) ? "1" : "0");
        if (!solver.getVarVal(input)) {
          // p = lit_neg(p);
          q = lit_neg(q);
          if (x == unroller.frame())
            m_lastFrame.push_back(false);
        }
        if (x == unroller.frame() - 1)
          m_lastFrame.push_back(true);

        // solver.addClause(&p, &p+1);
        solver.addClause(&q, &q + 1);
      }
    }
    outs() << "Size of last frame: " << m_lastFrame.size() << "\n";
  }

  vout().flush();
  return res;
}

template <typename Sat> void AvyBmc::getInputVals(Sat &s, Unroller<Sat> &unroller, vector<lit> &vals) {

    vals.clear();
    for (int i = 0; i < unroller.frames()-1; i++) {
        abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(i);

        int j, input;

        // -- in the first frame, first PI is the reset signal
        if (i == 0) {
            input = Vec_IntEntry(PIs, 0);
            // reset PI is on, current frame does not count
            if (s.getVarVal(input))
                continue;
        }

        Vec_IntForEachEntry(PIs, input, j) {
            // -- skipping the first input of the first and last
            // -- frames. It is used for reset and is not part of the
            // -- original circuit.
            if (j == 0 /*&& (i == 0 || i + 1 == unroller.frames ())*/)
                continue;
            vals.push_back(toLitCond(input, !s.getVarVal(input)));
        }
    }
}

template <typename Sat> void AvyBmc::printCex(Sat &s, Unroller<Sat> &unroller) {
  // -- skip cex if no output file is given
  if (gParams.cexFileName.empty())
    return;
  AVY_ASSERT(!gParams.stutter);
  AVY_ASSERT(gParams.tr0);

  VERBOSE(2, vout() << "Generating CEX: " << gParams.cexFileName << "\n";);
  boost::scoped_ptr<std::ofstream> pFout;
  std::ostream *pOut;

  if (gParams.cexFileName == "-")
    pOut = &outs();
  else {
    pFout.reset(new std::ofstream(gParams.cexFileName.c_str(), ofstream::out));
    pOut = pFout.get();
  }

  std::ostream &out = *pOut;
  out << "1\n"
      << "b0\n";
  int nRegs = Aig_ManRegNum(&*m_Aig);
  // HACK: stick_error adds an extra latch
  if (gParams.stick_error)
    nRegs--;

  for (int i = 0; i < nRegs; i++)
    out << "0";
  out << "\n";

  for (int i = 0; i < unroller.frames(); i++) {
    abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(i);

    int j, input;

    // -- in the first frame, first PI is the reset signal
    if (i == 0) {
      input = Vec_IntEntry(PIs, 0);
      // reset PI is on, current frame does not count
      if (s.getVarVal(input))
        continue;
    }

    Vec_IntForEachEntry(PIs, input, j) {
      // -- skipping the first input of the first frame
      // -- It is used for reset and is not part of the
      // -- original circuit.
      // -- TODO TR0
      if (j == 0 && i == 0)
        continue;
      out << (s.getVarVal(input) ? "1" : "0");
    }
    out << "\n";
    if (gParams.stick_error && i + 1 < unroller.frames()) {
      abc::Vec_Int_t *vOuts = unroller.getOutputs(i);
      int output = Vec_IntEntry(vOuts, Vec_IntSize(vOuts) - 1);
      if (s.getVarVal(output)) {
        VERBOSE(2, vout() << "Early CEX termination is untested!!!\n");
        // -- reached an early end of the counter-example
        break;
      }
    }
  }

  out << ".\n";
  out << std::flush;
}

} // namespace avy

static std::string parseCmdLine(int argc, char **argv) {
  po::options_description generic("Options");
  generic.add_options()("help", "print help message")(
      "print-params", "print current parameters")(
      "log,L", po::value<std::vector<std::string>>(), "log levels to enable")(
      "verbose,v", po::value<unsigned>(&gParams.verbosity)->default_value(0),
      "Verbosity level: 0 means silent")(
      "stutter,s",
      po::value<bool>(&gParams.stutter)
          ->default_value(false)
          ->implicit_value(true),
      "Stutter circuit instead of reseting to the initial state")(
      "tr0",
      po::value<bool>(&gParams.tr0)->default_value(true)->implicit_value(true),
      "Make only Tr0 be special (stutter or reset init)")(
      "coi",
      po::value<bool>(&gParams.coi)->default_value(true)->implicit_value(true),
      "add Tr logic based on COI")(
          "incr",
          po::value<bool>(&gParams.incr)
                  ->default_value(false)
                  ->implicit_value(true),
          "load clauses to solver incrementally")(
      "sat1",
      po::value<bool>(&gParams.sat1)
          ->default_value(false)
          ->implicit_value(true),
      "Always use satSolver (do not use satSolver2)")(
      "minisat",
      po::value<bool>(&gParams.minisat)
          ->default_value(false)
          ->implicit_value(true),
      "Use Minisat 2.2.0 for abstraction")(
      "glucose",
                            po::value<bool>(&gParams.glucose)
                             ->default_value(true)
                             ->implicit_value(true),
                              "Use Glucose for abstraction")(
      "stick-error",
      po::value<bool>(&gParams.stick_error)
          ->default_value(false)
          ->implicit_value(true),
      "Stick error output")(
      "depth", po::value<unsigned>(&gParams.maxFrame)->default_value(1),
      "BMC depth")(
      "dump-cnf", po::value<std::string>(&gCnfFile),
                   "File to dump CNF of the unrolling")(
      "bmc",
          po::value<bool>(&gDoBmc)->default_value(true)->implicit_value(true),
          "Do BMC")(
      "bmc_inc_ass",
          po::value<bool>(&gParams.bmc_incremental_assignment)->default_value(false)->implicit_value(true),
          "Construct assignment incrementally")(
      "sat-simp",
               po::value<bool>(&gParams.sat_simp)
                    ->default_value(false)
                    ->implicit_value(true),
         "Enable pre-processing for the non-interpolating SAT solver (if available)")(
      "glucose-inc-mode",
               po::value<bool>(&gParams.glucose_inc_mode)
                                      ->default_value(false)
                                      ->implicit_value(true),
                                  "Enable Glucose incremental mode")(
      "cex", po::value<std::string>(&gParams.cexFileName)->default_value(""),
      "Location to output counter-example")(
      "opt-bmc",
                   po::value<bool>(&gParams.opt_bmc)->default_value(true)->implicit_value(true),
                        "Enable optimized BMC");

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

    if (vm.count("print-params")) {
      outs() << gParams << "\n";
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

    VERBOSE(2, vout() << gParams << "\n";);

    return gParams.fName;
  } catch (std::exception &e) {
    outs() << "Error: " << e.what() << "\n";
    std::exit(1);
  }
}

int main(int argc, char **argv) {
  std::string fileName = parseCmdLine(argc, argv);
  AvyBmc bmc(fileName, gDoBmc, false);
  bmc.setCnfFile(gCnfFile);

  tribool res = bmc.run(gParams.maxFrame);

  Abc_Stop();

  if (res)
    return 1;
  else if (!res)
    return 0;
  else
    return 2;
}
