#include "AvyBmc2.h"

#include "AigUtils.h"
#include "Glucose.h"
#include "Minisat.h"
#include "Cadical.h"

#include "SafetyVC2.h"
#include "Unroller.h"

#include <avy/Util/AvyTribool.h>
#include "AigPrint.h"
#include "SafetyVC2.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"

#include "avy/Util/Stats.h"

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
  std::string cmd = "read " + fname + "; &get -n";
  Cmd_CommandExecute(pFrame, cmd.c_str());

  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pFrame);

  Gia_Man_t *pGia = Abc_FrameGetGia(pFrame);
  int i;
  Gia_Obj_t *pObj;
  Gia_ManForEachPi(pGia, pObj, i) {
      outs() << "PI: " << Gia_ObjCiName(pGia, i) << endl;
  }
  return Abc_NtkToDar(pNtk, 0, 1);
}

static std::string gCnfFile;
static bool gDoBmc;
static bool gBvMode;

AvyBmc2::AvyBmc2(std::string fname, bool doBmc = true)
    : m_FName(fname), m_doBmc(doBmc), m_bRes(false) , m_abs_lits(nullptr) {
  VERBOSE(2, vout() << "Starting ABC\n");
  Abc_Start();
  m_Aig = aigPtr(loadAig(fname));
}

AvyBmc2::AvyBmc2(Aig_Man_t *pAig,
                 bool cadical,
                 bool retAfterUnsat,
                 bool useAbs,
                 int realInputs,
                 std::vector<std::vector<std::pair<int,int>>> * abs_lits)
        : m_FName(""), 
        m_doBmc(true), 
        m_returnAfterUnsat(retAfterUnsat),
        m_bRes(false), 
        m_lastUnsatFrame(0),
        m_abs_lits(abs_lits),
        m_abstractionUsed(false),
        m_realInputs(realInputs),
        m_bUseAbs(useAbs) {
    VERBOSE(2, vout() << "Starting ABC\n");
    m_Aig = aigPtr(pAig);
    gParams.opt_bmc = true;
    gParams.incr = true;
    gParams.tr0 = true;
    gParams.sat_simp = true;
    gParams.coi = true;
    gParams.bmc_incremental_assignment = true;
    gParams.verbosity = 1;
    if (cadical) {
      gParams.cadical = true;
      gParams.glucose = false;
    } else {
      gParams.cadical = false;
      gParams.glucose = true;
    }
}

AvyBmc2::~AvyBmc2() { Abc_Stop(); }

tribool AvyBmc2::run(
  unsigned uDepth, 
  unsigned uStart, 
  std::vector<boost::dynamic_bitset<>> *inputVals) 
{
  Stats::set("Result", "UNKNOWN");
  VERBOSE(1, Stats::PrintBrunch(outs()););
  avy::tribool res = false;

  SafetyVC2 vc(&*m_Aig, gParams.opt_bmc,gParams.lemmaAbs,nullptr);

  m_bRes = false;
  if (gParams.glucose) {
    Glucose sat(2, gParams.sat_simp);
    Unroller<Glucose> unroller(sat, nullptr, false);
    return solve(vc, sat, unroller, uDepth, uStart, inputVals);
  } else if (gParams.cadical) {
    Cadical sat(5000, gParams.sat_simp);
    Unroller<Cadical> unroller(sat, nullptr, false);
    return solve(vc, sat, unroller, uDepth, uStart, inputVals);
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
avy::tribool AvyBmc2::solve(SafetyVC2 &vc, 
  Sat &solver, 
  Unroller<Sat> &unroller,
  unsigned uDepth, 
  unsigned uStart, 
  std::vector<boost::dynamic_bitset<>> *inputVals) 
{
  avy::tribool res = false;
  if (uStart > 0) {
        Stats::uset("Depth", uStart);
        VERBOSE(1, Stats::PrintBrunch(outs()););
        unrollTo(vc, solver, unroller, uStart-1);
    }
    if (inputVals != nullptr) {
        vector<lit> vals;
        generateHints(unroller, *inputVals, vals);
        solver.setHints(vals);
    }
    for (unsigned f = uStart; f <= uDepth; f++) {
      if (m_bUseAbs) {
          res = cegar_bmc(vc, solver, unroller, f);
      }
      else {
          res = bmc(vc, solver, unroller, f);
      }
      if (res) {
        if (!gParams.bmc_incremental_assignment || f == uDepth) {
          Stats::set("Result", "SAT");
          Stats::uset("Depth", f+1);
          VERBOSE(1, Stats::PrintBrunch(outs()););
          if (gBvMode)
              printCexBv(solver, unroller);
          else
              printCex(solver, unroller);
          return res;
        } else {
          Stats::set("Result", "SAT");
          Stats::uset("Depth", f+1);
          VERBOSE(1, Stats::PrintBrunch(outs()););
          vector<lit> vals;
          getInputVals(solver, unroller, vals);
          solver.setHints(vals);
        }
      }
      else if (!res) {
          Stats::set("Result", "UNSAT");
          Stats::uset("Depth", f+1);
          if (gParams.bmc_incremental_assignment) {
              m_lastUnsatFrame = f+1;
              if (m_returnAfterUnsat) {
                return res;
              }
          }
      }
      m_bRes = res;
    }
    if (res) {
      // printCex(sat, unroller);
      return res;
    }
}

template <typename Sat>
void AvyBmc2::unrollTo(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                       unsigned uDepth) {
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
            unroller.setDecisionVars(vars,false);
        }
    }
    // -- freeze current outputs
    unroller.setFrozenOutputs(uDepth, true);

    // -- add constraints for pBad into the last frame
    vc.addBad(unroller, pBad);
}

template <typename Sat>
tribool AvyBmc2::bmc(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                    unsigned uDepth) {
  AVY_MEASURE_FN;

  unrollTo(vc, solver, unroller, uDepth);

  IntVector assumptions;
  assumptions.push_back(unroller.getBadLit());
  int reset_input = Vec_IntGetEntry(unroller.getPrimaryInputs(0), 0);
  assumptions.push_back(toLitCond(reset_input, 1));

  cout << "Size of assumptions: " << assumptions.size() << endl;

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
            unroller.setDecisionVars(vars,true);
        }
    }
    VERBOSE(1, vout() << "Result: " << std::boolalpha << res << "\n");
    if (res) {
        Stats::set("Result", "SAT");
    }
    else if (!res) {
      lit p = lit_neg(assumptions[0]);
      solver.addClause(&p, &p + 1);
      Stats::set("Result", "UNSAT");
    }
  }

  vout().flush();
  return res;
}

template <typename Sat>
void AvyBmc2::prepareAbstraction(Unroller<Sat> &unroller, unsigned int uDepth) {
    if (m_abs_lits == nullptr) return;
    unsigned maxModule = ((uDepth + 1) / 2) + 1;
    std::vector<std::vector<std::pair<int,int>>> & vec = *m_abs_lits;
    AVY_ASSERT(maxModule <= vec.size());

    unsigned mulsNum = vec[0].size();

    Vec_Int_t *PIs = unroller.getPrimaryInputs(0);
    // Abstraction literals are ordered by module's depth
    for (unsigned i = m_abstraction.size() / mulsNum ; i < maxModule; i++) {
        vector<pair<int,int>> & lits = vec[i];
        AVY_ASSERT(lits.size() == mulsNum);
        for (unsigned j=0; j < mulsNum; j++) {
            unsigned lit_idx = lits[j].first+1;
            AVY_ASSERT(lits[j].first > 0);
            int input = Vec_IntGetEntry(PIs, lit_idx);
            m_abstraction.push_back(toLitCond(input, false));
        }
    }
}

template <typename Sat>
bool AvyBmc2::refineAbstraction(Sat &solver, Unroller<Sat> &unroller) {
    // Go over current assumptions, check if their value can be that of pout
    vector<abc::lit> vals;
    getInputVals(solver, unroller, vals);

    IntVector assumptions;
    assumptions.push_back(unroller.getBadLit());
    int reset_input = Vec_IntGetEntry(unroller.getPrimaryInputs(0), 0);
    assumptions.push_back(toLitCond(reset_input, 1));
    for (auto l : vals) {
        assumptions.push_back(l);
    }

    // We flip the abstraction literals so that the concrete model is considered
    for (auto l : m_abstraction) {
        if (!lit_sign(l))
            assumptions.push_back(lit_neg(l));
        else
            assumptions.push_back(l);
    }

    tribool res = solver.solve(assumptions);

    if (res) {
        // Counterexample is valid, no refinement
        return false;
    } else if (!res) {
        int *pCore;
        unsigned size = solver.core(&pCore);
        set<int> core;
        core.insert(pCore, pCore+size);
        cout << "Core size: " << size << endl;
        for (unsigned i = 0; i < m_abstraction.size(); i++) {
            int l = (m_abstraction[i]);
            if (core.find(l) != core.end() || core.find(lit_neg(l)) != core.end()) {
                VERBOSE(1, "Flipping an abstraction literal\n");
                if (!lit_sign(l))
                    m_abstraction[i] = lit_neg(l);
            }
        }
    }
    else {
        exit(-1);
    }
    return true;
}

template <typename Sat>
tribool AvyBmc2::cegar_bmc(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                     unsigned uDepth) {
    AVY_MEASURE_FN;

    unrollTo(vc, solver, unroller, uDepth);

    IntVector assumptions;
    assumptions.push_back(unroller.getBadLit());
    int reset_input = Vec_IntGetEntry(unroller.getPrimaryInputs(0), 0);
    assumptions.push_back(toLitCond(reset_input, 1));

    bool refined = true;
    tribool res = true;
    while (refined && res) {
        vout() << "Assumption is: " << unroller.getBadLit() << "\n";
        ScoppedStats _s_("solve");
        VERBOSE(1, vout() << "Solving " << uDepth << " ...\n" << std::flush;);

        prepareAbstraction(unroller, uDepth);
        IntVector i_assumptions(assumptions);
        i_assumptions.insert(i_assumptions.end(), m_abstraction.begin(), m_abstraction.end());

        for (lit Lit : i_assumptions) {
            solver.markSelector(lit_var(Lit), true);
        }

        res = solver.solve(i_assumptions);

        VERBOSE(1, vout() << "Result: " << std::boolalpha << res << "\n");
        if (res) {
            Stats::set("Result", "SAT");
            refined = refineAbstraction(solver, unroller);
        }
        else if (!res) {
            lit p = lit_neg(assumptions[0]);
            solver.addClause(&p, &p + 1);
            Stats::set("Result", "UNSAT");
        }
    }

    if (gParams.incr && gParams.coi) {
        for (unsigned i = 0; i <= uDepth; i++) {
            vector<int> vars;
            vc.getUncommitedInFrame(i, vars);
            unroller.setFrozenVars(vars, false);
            unroller.setDecisionVars(vars,true);
        }
    }

    vout().flush();
    return res;
}

template <typename Sat>
void AvyBmc2::generateHints(Unroller<Sat> &unroller, std::vector<boost::dynamic_bitset<>> & inputVals, vector<lit> &vals) {
    vals.clear();
    unsigned length = inputVals[0].size();
    assert(length < unroller.frames());
    for (unsigned i = 0; i < length; i++) {
        abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(i);

        int j, input;
        Vec_IntForEachEntry(PIs, input, j) {
            // -- skipping the first input of the first and last
            // -- frames. It is used for reset and is not part of the
            // -- original circuit.
            if (i == 0) {
                if (j == 0)
                    continue;
                else
                    vals.push_back(toLitCond(input, !inputVals[j - 1].test(i)));
            }
            else {
                vals.push_back(toLitCond(input, !inputVals[j].test(i)));
            }
        }
    }
}

template <typename Sat> void AvyBmc2::getInputVals(Sat &s, Unroller<Sat> &unroller, vector<lit> &vals) {

    vals.clear();
    for (int i = 0; i < unroller.frames()-1; i++) {
        abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(i);

        int j, input;

        // -- in the first frame, first PI is the reset signal
        if (i == 0) {
            input = Vec_IntEntry(PIs, 0);
            // reset PI is on, current frame does not count
            if (s.getVarVal(toLitCond(input,0)))
                continue;
        }

        Vec_IntForEachEntry(PIs, input, j) {
            // -- skipping the first input of the first and last
            // -- frames. It is used for reset and is not part of the
            // -- original circuit.
            if (j == 0 && i == 0/*&& (i == 0 || i + 1 == unroller.frames ())*/)
                continue;
            if (i == 0 && j == m_realInputs) break;
            if ( i > 0 && j == m_realInputs-1) break;
            vals.push_back(toLitCond(input, !s.getVarVal(input)));
        }
    }
}

template <typename Sat> void AvyBmc2::printCex(Sat &s, Unroller<Sat> &unroller) {
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
      // -- skipping the first input of the first and last
      // -- frames. It is used for reset and is not part of the
      // -- original circuit.
      if (j == 0 && i == 0/*&& (i == 0 || i + 1 == unroller.frames ())*/)
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

template <typename Sat> void AvyBmc2::printCexBv(Sat &s, Unroller<Sat> &unroller) {
    // -- skip cex if no output file is given
    if (gParams.cexFileName.empty())
        return;
    AVY_ASSERT(!gParams.stutter);
    AVY_ASSERT(gParams.tr0);
    AVY_ASSERT(!gParams.stick_error);

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

    Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pFrame);

    char **ppNames = Abc_NtkCollectCioNames(pNtk, 0);
    unsigned numPIs = Abc_NtkPiNum(pNtk);
    vector<string> names;
    for (unsigned pi=0; pi < numPIs; pi++) {
        names.push_back(ppNames[pi]);
    }
    delete ppNames;

    vector<dynamic_bitset<>> vals;
    vals.resize(numPIs);
    for (int i = 0; i < unroller.frames(); i++) {
        abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(i);

        if (i == 0) {
            AVY_ASSERT(numPIs+1 == Vec_IntSize(PIs));
        }
        else {
            AVY_ASSERT(numPIs == Vec_IntSize(PIs));
        }

        int j, input;

        // -- in the first frame, first PI is the reset signal
        if (i == 0) {
            input = Vec_IntEntry(PIs, 0);
            // reset PI is on, current frame does not count
            if (s.getVarVal(input)) {
                errs() << "Reset Input is ON in first frame - bailing out\n";
                AVY_ASSERT(false);
                continue;
            }
        }

        Vec_IntForEachEntry(PIs, input, j) {
            // -- skipping the first input of the first and last
            // -- frames. It is used for reset and is not part of the
            // -- original circuit.
            if (i == 0) {
                if (j > 0) {
                    vals[j - 1].push_back(s.getVarVal(input));
                    out << (s.getVarVal(input) ? "1" : "0");
                }
            }
            else {
                vals[j].push_back(s.getVarVal(input));
                out << (s.getVarVal(input) ? "1" : "0");
            }
        }
        out << "\n";
    }

    for (unsigned pi = 0; pi < numPIs; pi++) {
        dynamic_bitset<> & piVal = vals[pi];
        std::stringstream stream;
        stream << std::hex << piVal.to_ulong();
        std::string result( stream.str() );

        //out << "(define-fun " << names[pi] << " () (_ BitVec 16) #x" << std::hex << piVal.to_ulong()  << ")\n";

        out << "(assert (= " << names[pi] << " (_ bv" <<
            std::dec << piVal.to_ulong() << " " <<
            std::dec << vals[pi].size() << ")))" << endl;
        vals[pi].clear();
    }
    vals.clear();

    out << std::flush;
    out.flush();
}
