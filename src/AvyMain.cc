#include "AvyMain.h"
#include "AigPrint.h"
#include "AvyQuip.h"
#include "SafetyVC.h"
#include "avy/Util/Global.h"
#include "avy/Util/Utils.h"
#include "boost/lexical_cast.hpp"

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"

#include "ItpValidator.h"
#include "Unroller.h"
#include "boost/scoped_ptr.hpp"
#include "simp/SimpSolver.h"

#include "AvyTrace.h"
#include "AvyUnsatCore.h"

#include "boost/format.hpp"
#include <fstream>
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
  string cmd = "read " + fname;
  Cmd_CommandExecute(pFrame, cmd.c_str());

  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pFrame);

  return Abc_NtkToDar(pNtk, 0, 1);
}

namespace avy {
AvyMain::AvyMain(std::string fname) : m_fName(fname), m_Vc(0), m_pPdr(0) {
  VERBOSE(2, vout() << "Starting ABC\n");
  Abc_Start();
  m_Aig = aigPtr(loadAig(fname));
  m_lemmaLevel = 0;
  m_TraceMan = new AvyTrace();
  // m_pPdr = new Pdr (&*m_Aig);
}

AvyMain::AvyMain(AigManPtr pAig)
        : m_fName(std::string()), m_Aig(pAig), m_Vc(0), m_pPdr(0) {
    VERBOSE(2, vout() << "Starting ABC\n");
    Abc_Start();
    m_lemmaLevel = 0;
    m_TraceMan = new AvyTrace();
    // m_pPdr = new Pdr (&*m_Aig);
}
AvyMain::AvyMain(AigManPtr pAig, AvyTrace* Trace)
        : m_fName(std::string()), m_Aig(pAig), m_Vc(0), m_pPdr(0) {
    VERBOSE(2, vout() << "Starting ABC\n");
    Abc_Start();
    m_lemmaLevel = 0;
    m_TraceMan = Trace;
    // m_pPdr = new Pdr (&*m_Aig);
}

AvyMain::~AvyMain() {
  if (m_pPdr) delete m_pPdr;
  if (m_TraceMan) delete m_TraceMan;
  //Abc_Stop();
}

int AvyMain::run() {
  Muser2 muser(2);
  Muser2 *musPtr = gParams.min_muser ? &muser : nullptr;
  if (gParams.minisat_itp) {
    ItpMinisat solver(2, 2, gParams.itp_simp);
    Unroller<ItpMinisat> unroller(solver, musPtr,
                                  gParams.min_suffix || gParams.abstraction ||
                                      !gParams.lemmaAbs);
    return run(solver, muser, unroller);
  } else if (gParams.cadical_itp) {
    ItpCadical solver(2, 2, gParams.itp_simp);
    Unroller<ItpCadical> unroller(solver, musPtr,
                                  gParams.min_suffix || gParams.abstraction ||
                                      !gParams.lemmaAbs);
    return run(solver, muser, unroller);
  } else if (gParams.glucose_itp) {
    ItpGlucose solver(2, 2, gParams.itp_simp);
    Unroller<ItpGlucose> unroller(solver, musPtr,
                                  gParams.min_suffix || gParams.abstraction ||
                                      !gParams.lemmaAbs);
    return run(solver, muser, unroller);
  } else {
    assert(false);
  }
  return 0;
}

template <typename Sat>
int AvyMain::run(Sat &solver, Muser2 &muser, Unroller<Sat> &unroller) {
  VERBOSE(
      1,
      if (gParams.kStep > 1 && !gParams.stutter && !gParams.stick_error) vout()
          << "Warning: using kStep>1 without stuttering "
          << "or stick-error is unsound\n";);

  SafetyVC2 vc(&*m_Aig, gParams.opt_bmc, gParams.lemmaAbs, m_TraceMan);
  m_Vc = &vc;
  UnsatCoreComputer<Sat> unsatCoreComputer(&unroller, &solver, &muser, m_Vc);

  m_pPdr = new Pdr(&*m_Aig);
  m_pPdr->setQuipMode(false);

  unsigned nTriviallyPushed = 0;
  unsigned nMaxFrames = gParams.maxFrame;
  unsigned nLastReset = 0;
  for (unsigned nFrame = 0; nFrame < nMaxFrames; nFrame += gParams.kStep) {
    ScoppedStats loopStats(string(__FUNCTION__) + ".loop");
    Stats::set("Result", "UNKNOWN");
    VERBOSE(2, Stats::PrintBrunch(vout()););
    Stats::count("Frame");
    Stats::uset("Depth", nFrame);

    if (nFrame >= ((unsigned int)gParams.pdr)) {
      VERBOSE(2, m_pPdr->setVerbose(true));
      int res = m_pPdr->solve();
      VERBOSE(1, m_pPdr->statusLn(vout()));
      Stats::uset("lemmas", m_pPdr->getNumLemmas());
      Stats::uset("k-ind-lemmas", m_pPdr->getNumLemmas(true));
      if (res == 1) {
        // vout () << "SAFE\n";
        outs() << "0";
        Stats::set("Result", "UNSAT");
        return m_pPdr->validateInvariant() ? 0 : 3;
      } else if (res == 0) {
        outs() << "1";
        Stats::set("Result", "SAT");
        return 1;
      } else {
        Stats::set("Result", "UNKNOWN");
        vout() << "UNKNOWN\n";
        return 2;
      }
    }

    tribool res =
        doBmc(nFrame, solver, muser, unroller, nullptr, &unsatCoreComputer);
    if (res) {
      VERBOSE(1, vout() << "SAT from BMC at frame: " << nFrame << "\n";);
      Stats::set("Result", "SAT");
      printCex(solver, unroller);
      Stats::uset("lemmas", m_pPdr->getNumLemmas());
      Stats::uset("k-ind-lemmas", m_pPdr->getNumLemmas(true));
      return 1;
    } else if (!res) {
      VERBOSE(1, vout() << "UNSAT from BMC at frame: " << nFrame << "\n";);

      if (m_LastCoreSize == 0)
        nTriviallyPushed++;
      else
        nTriviallyPushed = 0;

      vector<int> vVarToId;
      AigManPtr itp = aigPtr(solver.getInterpolant(unroller.getBadLit(),
                                                   unroller.getAllOutputs(),
                                                   Saig_ManRegNum(&*m_Aig)));

      Stats::uset("OrigItp", Aig_ManAndNum(&*itp));
      //-- simplify
      if (gParams.itp_simplify) {
        itp = aigPtr(Aig_ManSimplifyComb(&*itp));
        Stats::uset("SimpItp", Aig_ManAndNum(&*itp));
        VERBOSE(2, Aig_ManPrintStats(&*itp));
      }
      VERBOSE(3, Stats::PrintBrunch(vout()););

      // -- extend itp with additional equivalences to make it into a
      // -- true interpolant
      if (gParams.opt_bmc && m_LastCoreSize > 0) {
        // HG: During encoding, when we simplify Tr of a frame,
        // HG: we use the equivalence information from the previous frame.
        // HG: However, when validating, we do not add Tr to any previous frames
        // HG: and therefore cannot simplify Tr with equivalence information
        // from previous frame. HG: This wouldn't work
        // AVY_ASSERT(validateItp(itp, true));
        std::vector<IntVector> equivs = m_Vc->getFrameEquivs();
        findItpConstraints(itp, equivs, NULL);
      }

      AVY_ASSERT(validateItp(itp));

      unsigned beginning = 0, end = 0;
      unsigned lbeginning = 0, lend = 0;
      if (m_pPdr->maxFrames() > nFrame) {
        beginning = m_pPdr->getNumLemmas();
        lbeginning = m_pPdr->getNumberOfLiterals();
        VERBOSE(2, vout() << "Number of lemmas at the beginning: " << beginning
                          << std::endl;);
      }
      if (doPdrTrace(itp)) {
        m_pPdr->setSafeLevel(nFrame);
        outs() << "0\nb0\n.\n";
        VERBOSE(1, m_pPdr->statusLn(vout()););
        Stats::set("Result", "UNSAT");
        VERBOSE(4, m_pPdr->printCubesInfo(-1));
        VERBOSE(4, m_pPdr->findStrongerCubes());
        Stats::uset("lemmas", m_pPdr->getNumLemmas());
        Stats::uset("k-ind-lemmas", m_pPdr->getNumLemmas(true));
        printInvCert(gParams.certificate);
        return m_pPdr->validateInvariant() ? 0 : 3;
      }

      end = m_pPdr->getNumLemmas();
      lend = m_pPdr->getNumberOfLiterals();
      Stats::uset("LemmasLearned", end > beginning ? end - beginning : 0);
      Stats::uset("LiteralsLearned", lend > lbeginning ? lend - lbeginning : 0);
      VERBOSE(2,
              vout() << "Number of lemmas at the end: " << end << std::endl;);
      m_pPdr->setSafeLevel(nFrame);

      Vec_Ptr_t *pCubesNew = Vec_PtrAlloc(16);
      int j;
      Pdr_Set_t *pNewCube;
      for (int f = 1; f <= nFrame; f++) {
        m_pPdr->getCoverDeltaCubes(f, pCubesNew);
        Vec_PtrForEachEntry(Pdr_Set_t *, pCubesNew, pNewCube, j) {
          if (pNewCube->nDepth == 0) pNewCube->nDepth = (nFrame - f) + 1;
        }
        Vec_PtrClear(pCubesNew);
      }
      Vec_PtrFree(pCubesNew);

      doStrengthenVC();
      unsigned score = m_pPdr->getFrameAvgAge(nFrame);
      VERBOSE(2, vout() << "\tFrame is: " << nFrame
                        << " and the average age is: " << score << std::endl;);
      if (score + nLastReset > nFrame) {
        VERBOSE(2, vout() << "\t"
                          << "Average age is: " << score
                          << " and last reset was at: " << nLastReset
                          << std::endl;);
        nLastReset = nFrame;
        continue;
      }
      if (nTriviallyPushed >= 3) continue;

      if (gParams.quip &&
          (((end - beginning < (100 / getLuby(nFrame + 1))) ||
            ((double)beginning * 1.5) >= (double)end * getLuby(nFrame + 1)))) {
        m_pPdr->setQuipMode(true);
        if (doQuip(nFrame, solver, muser, unroller, unsatCoreComputer)) {
          m_pPdr->printCubesInfo(-1);
          Stats::uset("lemmas", m_pPdr->getNumLemmas());
          Stats::uset("k-ind-lemmas", m_pPdr->getNumLemmas(true));
          return m_pPdr->validateInvariant() ? 0 : 3;
        }
        m_pPdr->setQuipMode(false);
        solver.setBudget(-1);
      }
    } else {
      VERBOSE(1, vout() << "UNKNOWN from BMC at frame: " << nFrame << "\n";);
      return 2;
    }
  }
  return 3;
}

/// Strengthen VC using current PDR trace
void AvyMain::doStrengthenVC() {
  AVY_MEASURE_FN;
  m_Vc->resetPreCond();
  Vec_Ptr_t *pCubes = Vec_PtrAlloc(16);

  /**
                  I0      I1      I2
     Init & TR(0) & TR(1) & TR(2) & Bad
          F0      F1      F2      F3
     add F1 to pre of TR(1), F2 to pre of TR(2), etc.
   */

  /*Aig_Man_t* pAig = Aig_ManStart( 5000 );
  for (int i=0; i < m_Aig->nRegs; i++)
      Aig_ObjCreateCi(pAig);
  Aig_Obj_t* pCo = Aig_ObjCreateCo(pAig, Aig_ManConst1(pAig));*/

  // for each lemma in pdr trace, try adding to the global trace
  // very expensive
  for (unsigned i = 1; i < m_pPdr->maxFrames(); ++i) {
    Vec_PtrClear(pCubes);
    m_pPdr->getCoverDeltaCubes(i, pCubes);
    Pdr_Set_t *pCube;
    int j;
    Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) {
      AvyLemma &lemma = m_TraceMan->mkLemma(
          pCube->Lits, (pCube->Lits) + pCube->nLits, i, true);
      AVY_ASSERT(lemma.getFrame() >= i);
      m_Vc->addPreCondClause(&lemma, lemma.getFrame());
    }
    // Aig_Obj_t* p = m_pPdr->getCover(i, pAig);
    // Aig_ObjDisconnect(pAig, pCo);
    // Aig_ObjConnect(pAig, pCo, p, NULL);
    // m_Vc->resimplifyFrame(pAig, i-1);
  }
  Vec_PtrClear(pCubes);
  m_pPdr->getInvarCubes(pCubes);
  Pdr_Set_t *pCube;
  int j;
  Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) {
    AvyLemma &lemma = m_TraceMan->mkLemma(
        pCube->Lits, (pCube->Lits) + pCube->nLits, m_pPdr->maxFrames(), true);
    lemma.setInv();
    m_Vc->addPreCondClause(&lemma, m_pPdr->maxFrames());
  }
  Vec_PtrFree(pCubes);
}

/// convert interpolant into PDR trace
tribool AvyMain::doPdrTrace(AigManPtr itp, bool dropLast) {
  AVY_MEASURE_FN;
  AVY_MEASURE_FN_LAST;

  VERBOSE(1, vout() << "Building PDR trace\n");
  unsigned itpSz = Aig_ManCoNum(&*itp);
  if (dropLast) itpSz--;
  m_pPdr->ensureFrames(m_lemmaLevel + 2);
  // The frame should satisfy initiation. Therefore,
  // m_pPdr->getSafeLevel()>=m_lemmaLevel
  AVY_ASSERT(m_pPdr->getSafeLevel() >= m_lemmaLevel);
  for (unsigned i = 0; i < itpSz; ++i) {
    if (i < m_lemmaLevel) {
      VERBOSE(2, vout() << "converting to delta trace (k-ind): " << i << " "
                        << m_lemmaLevel + 1 << "\n";);
      // -- skip if true
      if (Aig_ObjFanin0(Aig_ManCo(&*itp, i)) == Aig_ManConst1(&*itp)) continue;

      AigManPtr prevMan = aigPtr(Aig_ManStartFrom(&*itp));
      Aig_Obj_t *pPrev;
      pPrev =
          i == 0 ? Aig_ManConst0(&*prevMan) : m_pPdr->getCover(i, &*prevMan);
      Aig_ObjCreateCo(&*prevMan, pPrev);
      pPrev = NULL;

      AigManPtr dupMan = aigPtr(Aig_ManDupSinglePo(&*itp, i, false));
      AigManPtr orMan = aigPtr(Aig_ManCreateMiter(&*dupMan, &*prevMan, 2));

      dupMan.reset();
      prevMan.reset();
      AigManPtr newTr = aigPtr(Aig_ManReplacePo(&*m_Aig, &*orMan, true));
      newTr = aigPtr(Aig_ManGiaDup(&*newTr));

      Stats::resume("doPdrTrace_part3");
      Pdr pdr(&*newTr);
      pdr.get()->fQuipMode = m_pPdr->get()->fQuipMode;

      Vec_Ptr_t *pCubes = Vec_PtrAlloc(16);
      pdr.setLimit(3);
      m_pPdr->getCoverDeltaCubes(m_lemmaLevel, pCubes);
      pdr.addCoverCubes(1, pCubes);
      Vec_PtrClear(pCubes);
      m_pPdr->getCoverDeltaCubes(m_lemmaLevel + 1, pCubes);
      LOG("trace_size", logs() << "(kind) Number of lemmas at frame "
                               << m_lemmaLevel + 1 << " " << Vec_PtrSize(pCubes)
                               << endl;);
      pdr.addCoverCubes(2, pCubes);
      Vec_PtrClear(pCubes);
      m_pPdr->getCoverCubes(m_lemmaLevel + 2, pCubes, false);
      pdr.addCoverCubes(3, pCubes);
      Vec_PtrClear(pCubes);
      // -- move invariants over
      m_pPdr->getInvarCubes(pCubes);
      pdr.addInvarCubes(pCubes);
      Vec_PtrClear(pCubes);
      Stats::stop("doPdrTrace_part3");

      pdr.setVerbose(false);
      pdr.setGenConfLimit(gParams.genConfLimit);
      {
        Stopwatch solveSafeTime;
        solveSafeTime.start();
        pdr.solveSafe(true);
        LOG("trace_size",
            logs() << "Time for solve Safe "
                   << (boost::format("%.2f") % (solveSafeTime).toSeconds())
                   << endl;);
      }
      pdr.getCoverDeltaCubes(2, pCubes);
      int j;
      Pdr_Set_t *pCube;
      Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) {
        if (pCube->nOrigF == 0) pCube->nOrigF = m_lemmaLevel + 1;
        if (pCube->nDepth == 0) pCube->nDepth = (itpSz - 1) - m_lemmaLevel;
      }
      if (gParams.reset_cover) m_pPdr->resetCover(m_lemmaLevel + 1);
      m_pPdr->addCoverCubes(m_lemmaLevel + 1, pCubes);
      LOG("trace_size", logs() << "(kind) Number of lemmas at frame "
                               << m_lemmaLevel + 1 << " " << Vec_PtrSize(pCubes)
                               << endl;);
      Vec_PtrClear(pCubes);
      // -- move invariants
      if (gParams.reset_cover) m_pPdr->resetInvar();
      pdr.getInvarCubes(pCubes);
      m_pPdr->addInvarCubes(pCubes);
      Vec_PtrFree(pCubes);
      pCubes = NULL;
      VERBOSE(1, m_pPdr->statusLn(vout()););
    } else {
      VERBOSE(2, vout() << "converting to delta trace: " << i << " " << i + 1
                        << "\n";);
      m_pPdr->ensureFrames(i + 2);
      // -- skip if true
      if (Aig_ObjFanin0(Aig_ManCo(&*itp, i)) == Aig_ManConst1(&*itp)) continue;

      AigManPtr prevMan = aigPtr(Aig_ManStartFrom(&*itp));
      Aig_Obj_t *pPrev;
      pPrev =
          i == 0 ? Aig_ManConst0(&*prevMan) : m_pPdr->getCover(i, &*prevMan);
      Aig_ObjCreateCo(&*prevMan, pPrev);
      pPrev = NULL;

      Stats::resume("doPdrTrace_part1");
      AigManPtr dupMan = aigPtr(Aig_ManDupSinglePo(&*itp, i, false));
      AigManPtr orMan = aigPtr(Aig_ManCreateMiter(&*dupMan, &*prevMan, 2));

      dupMan.reset();
      prevMan.reset();

      AigManPtr newTr = aigPtr(Aig_ManReplacePo(&*m_Aig, &*orMan, true));
      newTr = aigPtr(Aig_ManGiaDup(&*newTr));
      Stats::stop("doPdrTrace_part1");
      Stats::resume("doPdrTrace_part2");

      Pdr pdr(&*newTr);
      pdr.get()->fQuipMode = m_pPdr->get()->fQuipMode;

      Vec_Ptr_t *pCubes = Vec_PtrAlloc(16);
      pdr.setLimit(i == 0 ? 2 : 3);
      if (i >= 1) {
        m_pPdr->getCoverDeltaCubes(i, pCubes);
        pdr.addCoverCubes(1, pCubes);
        Vec_PtrClear(pCubes);
      }

      m_pPdr->getCoverDeltaCubes(i + 1, pCubes);
      LOG("trace_size", logs() << "Number of lemmas at frame " << i + 1 << " "
                               << Vec_PtrSize(pCubes) << endl;);
      pdr.addCoverCubes(i == 0 ? 1 : 2, pCubes);
      Vec_PtrClear(pCubes);
      m_pPdr->getCoverCubes(i + 2, pCubes, false);
      pdr.addCoverCubes(i == 0 ? 2 : 3, pCubes);
      Vec_PtrClear(pCubes);
      // -- move invariants over
      m_pPdr->getInvarCubes(pCubes);
      pdr.addInvarCubes(pCubes);
      Vec_PtrClear(pCubes);
      Stats::stop("doPdrTrace_part2");

      // m_pPdr->printCubesInfo(i+1);
      pdr.setVerbose(false);
      pdr.setGenConfLimit(gParams.genConfLimit);
      {
        Stopwatch solveSafeTime;
        solveSafeTime.start();
        pdr.solveSafe();
        LOG("trace_size",
            logs() << "Time for solve Safe "
                   << (boost::format("%.2f") % (solveSafeTime).toSeconds())
                   << endl;);
      }

      Vec_PtrClear(pCubes);
      pdr.getCoverDeltaCubes(i == 0 ? 1 : 2, pCubes);
      if (gParams.reset_cover && i >= 1) m_pPdr->resetCover(i + 1);
      int j;
      Pdr_Set_t *pCube;
      Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) {
        if (pCube->nOrigF == 0) pCube->nOrigF = i + 1;
        if (pCube->nDepth == 0) pCube->nDepth = itpSz - i;
      }
      LOG("trace_size", logs() << "Number of lemmas at frame " << i + 1 << " "
                               << Vec_PtrSize(pCubes) << endl;);
      m_pPdr->addCoverCubes(i + 1, pCubes);
      // -- move invariants
      // HG: since we are not pushing,
      // HG: there is no way there are new invariants
      // HG: not adding anything to the global database
      if (gParams.reset_cover) m_pPdr->resetInvar();
      Vec_PtrClear(pCubes);
      pdr.getInvarCubes(pCubes);
      m_pPdr->addInvarCubes(pCubes);
      Vec_PtrFree(pCubes);
      pCubes = NULL;
      // m_pPdr->printCubesInfo(i+1);

      int kMin = gParams.shallow_push ? i + 1 : 1;
      int kMax = 0;
      // create place for pushing
      m_pPdr->ensureFrames(i + 2);
      Stats::uset("lemmas", m_pPdr->getNumLemmas());
      Stats::uset("k-ind-lemmas", m_pPdr->getNumLemmas(true));
      if (m_pPdr->push(kMin, kMax)) return true;

      VERBOSE(1, m_pPdr->statusLn(vout()););
    }
  }
  // XXX this might not always be the case.  For example, when
  // XXX doPdrTrace is called on a conjecture before it is called on a
  // XXX property
  if (!dropLast) m_pPdr->setSafeLevel(itpSz);

  if ((gParams.shallow_push ||
       Aig_ObjFanin0(Aig_ManCo(&*itp, itpSz - 1)) == Aig_ManConst1(&*itp)) &&
      m_pPdr->push())
    return true;

  AVY_ASSERT(m_pPdr->validateTrace());
  return tribool();
}

template <typename Sat>
tribool AvyMain::doBmc(unsigned nFrame, Sat &solver, Muser2 &muser,
                       Unroller<Sat> &unroller, AigManPtr pBad,
                       UnsatCoreComputer<Sat> *unsatCoreComputer) {
  AVY_MEASURE_FN;

  m_LastCoreSize = 0;
  m_Core.clear();
  tribool res =
      solveWithCore(solver, muser, unroller, nFrame, pBad, unsatCoreComputer);
  return res;
}

template <typename Sat>
avy::tribool AvyMain::solveWithCore(Sat &sat, Muser2 &muser,
                                    Unroller<Sat> &unroller, unsigned nFrame,
                                    AigManPtr pBad,
                                    UnsatCoreComputer<Sat> *unsatCoreComputer) {
  AVY_MEASURE_FN;
  if (!gParams.incr) {
    // --  reset the unroller and VC. Non-incremental mode.
    muser.reset(2);
    sat.reset(2, 2);
    if (gParams.min_muser)
      unroller.reset(&sat, &muser);
    else
      unroller.reset(&sat, nullptr);
    m_Vc->reset();
    doStrengthenVC();
  }
  // -- reset info about last frame. It was used for Bad in the
  // -- previous iteration
  unroller.resetLastFrame();

  // TODO: Figure out a way to un-freeze output from previous frame

  if (!gParams.coi) {
    ScoppedStats _s_("bmc_unroll");
    for (unsigned i = unroller.frame(); i <= nFrame; ++i) {
      // -- add Tr logic to unroller and the underlying sat-solver
      m_Vc->addTr(unroller);
      // HG : If there were new lemmas added to previous frames
      // HG : we ignore them non coi plus incr mode
      unroller.newFrame();
    }
  } else {
    ScoppedStats _s_("bmc_unroll");
    if (pBad == nullptr) { pBad = m_Vc->getBad(); }
    // -- assuming that the first output of pBad is the bad output
    vector<int> bad(1, 0);
    IntVector support;
    Aig_GetSupport(&*pBad, bad, support);
    if (unroller.frame() > nFrame) {
      // -- when doing QUIP, the unroller is already unrolled enough
      // -- so just calculate the support at the required frame
      // HG : nFrame is always equal to unroller.frame()-1
      m_Vc->addTrLogicRec(unroller, support, nFrame);
      m_Vc->addCondLogicRec(unroller, nFrame);
    } else {
      for (unsigned i = unroller.frame(); i <= nFrame; ++i) {
        // -- set up frames and unroller
        m_Vc->setupFrame(unroller);
        // -- last iteration: add COI of bad
        if (i == nFrame) {
          m_Vc->addTrLogicRec(unroller, support);
          m_Vc->addCondLogicRec(unroller);
        }
        unroller.newFrame();
      }
    }
  }
  // -- freeze current outputs
  unroller.setFrozenOutputs(nFrame, true);

  // -- add constraints for pBad into the last frame
  m_Vc->addBad(unroller, pBad);

  lit badLit = unroller.getBadLit();
  unroller.addAssump(badLit);
  if (gParams.min_muser) {
    // -- assert bad literal in muser
    muser.addClause(&badLit, &badLit + 1, badLit);
  }
  // -- mark assumptions as selectors
  // -- this will freeze them
  for (lit Lit : unroller.getAssumps()) {
    sat.markSelector(lit_var(Lit), true);
  }

  // -- solve
  tribool res;
  {
    ScoppedStats _s_("bmc_solve");
    res = sat.solve(unroller.getAssumps());
  }

  if (res.undef()) return res;
  if (res) return res;
  IntVector core = unsatCoreComputer->computeUNSATCore();
  m_lemmaLevel = unsatCoreComputer->getLemmaLevel();
  // The frame should satisfy initiation
  AVY_ASSERT(m_pPdr->getSafeLevel() >= m_lemmaLevel);
  // core.size includes badLit
  m_LastCoreSize = core.size() - 1;
  return false;
}

template <typename Sat>
tribool AvyMain::doQuip(unsigned nFrame, Sat &solver, Muser2 &muser,
                        Unroller<Sat> &unroller,
                        UnsatCoreComputer<Sat> &unsatCoreComputer) {
  AvyQuip quip(*this);
  return quip(nFrame, solver, muser, unroller, unsatCoreComputer);
}

void AvyMain::addPreCond(SafetyVC2 &vc, int nFrame) {
  // copy all pointers from m_Vc preCond to vc preCond
  AVY_MEASURE_FN;
  vc.modifyPreCond(nFrame) = m_Vc->getPreCond(nFrame);
}

bool AvyMain::validateItp(AigManPtr itp, bool propagate) {
  ItpValidator<> v(propagate);
  return v(&*itp, &*m_Aig, *m_TraceMan, m_lemmaLevel);
}

template <typename Sat>
void AvyMain::printCex(Sat &s, Unroller<Sat> &unroller) {
  // -- skip cex if no output file is given
  if (gParams.cexFileName.empty()) return;

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
  if (gParams.stick_error) nRegs--;

  for (int i = 0; i < nRegs; i++) out << "0";
  out << "\n";

  for (int i = 0; i < unroller.frames(); i++) {
    abc::Vec_Int_t *PIs = unroller.getPrimaryInputs(i);

    int j, input;

    // -- in the first frame, first PI is the reset signal
    if (i == 0) {
      input = Vec_IntEntry(PIs, 0);
      // reset PI is on, current frame does not count
      if (s.getVarVal(input)) continue;
    }

    Vec_IntForEachEntry(PIs, input, j) {
      // -- skipping the first input of the first and last
      // -- frames. It is used for reset and is not part of the
      // -- original circuit.
      if (j == 0 && i == 0/*&& (i == 0 || i + 1 == unroller.frames ())*/) continue;
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

/**
   Rebuild itp with additional equivalences on which it implicitly relies
 */
// AG: this function needs a cleanup pass
bool AvyMain::findItpConstraints(AigManPtr &itp,
                                 std::vector<IntVector> &equivFrames,
                                 AigManPtr pBad) {

  /**
     let Itp1 and Itp2 be two successive interpolants in a sequence
     We know that

        Itp1 & SimpTr ==> Itp2

        Itp1 & Equivs1 & Tr ==> Itp2

     where Equivs1 are some equivalences (i.e., equalities between
     pair of registers or a register an a constant)

     This method finds a subset E1 of Equivs1 such that

        Itp1 & E1 & Tr ==> Itp2

     holds. Itp1 is then extended with E1.

     The computation proceeds backwards

     E1 is computed by unsat core.

     TODO The method should be re-factored so that the inner computation is
     clearer.
     Unsat core can be computed by variety of methods (e.g., using muser)

     New equivalences are currently added into Itp via Aig. This is
     needed because we need CNF for the negation of the updated Itp at
     the next step of the computation.

   */

  AVY_MEASURE_FN;
  VERBOSE(1, vout() << "FINDING NEEDED CONSTRAINTS: ";);

  unsigned coNum = Aig_ManCoNum(&*itp);
  VERBOSE(1, vout() << "CoNum: " << coNum << " EquivNum: " << equivFrames.size()
                    << "\n";);

  bool bChanged = true;
  CnfPtr cnfItp;

  for (unsigned int i = coNum; i > 0; --i) {
    // Need to rederive the CNF in case it was changed
    if (bChanged) {
      cnfItp = cnfPtr(AvyCnf_Derive(&*itp, Aig_ManCoNum(&*itp)));
      bChanged = false;
    }

    Glucose satSolver(2, false, true);
    Unroller<Glucose> unroller(satSolver);
    SafetyVC2 vc(&*m_Aig, false, false, nullptr);
    // -- fast forward the unroller and VC to the right frame
    while (i >= 2 && unroller.frame() < i - 1) unroller.newFrame();
    /*
        A map from a register to an assumption literal guarding its
        equivalence. For example, if register 2 is equivalent to
        register 5, the constraint in sat-solver might be,

          a ==> (v2 == v5)

        where `a' is an assumption literal, `v2' and `v5' are sat-vars
        for the registers. Then, `equivToLit[2] == a'.
    */
    vector<lit> equivToLit;
    if (i >= 1) {
      // XXX AG: shift cnfItp by offset from freshBlock
      // XXX AG: in most cases, the offset is 0 which is why this
      // XXX AG: might work for now
      unsigned nOffset = unroller.freshBlock(cnfItp->nVars);
      ScoppedCnfLift scLift(cnfItp, nOffset);
      unroller.addCnf(&*cnfItp);

      // -- assert Itp_{i-1}
      lit Lit = toLit(cnfItp->pVarNums[Aig_ManCo(&*itp, i - 1)->Id]);
      satSolver.addClause(&Lit, &Lit + 1);

      // -- register outputs
      Aig_Obj_t *pCi;
      int j;
      Aig_ManForEachCi(&*itp, pCi, j) {
        unroller.addOutput(cnfItp->pVarNums[pCi->Id]);
      }

      // Take care of equivalence constraints
      const vector<int> &equiv_i = equivFrames[i - 1];
      bool bNoConstraints = std::all_of(equiv_i.begin(), equiv_i.end(),
                                        [](int x) { return x == -1; });
      if (bNoConstraints) {
        // if the current interpolant is a constant and there are no
        // equivalence, we are done
        if (Aig_ObjFanin0(Aig_ManCo(&*itp, i - 1)) == Aig_ManConst1(&*itp))
          break;
        // if there are no equivalences, nothing to compute, move to next itp
        VERBOSE(1, vout() << "." << std::flush;);
        continue;
      }

      // generate constraints for equivalences
      equivToLit.resize(equiv_i.size(), -1);
      for (unsigned j = 0; j < equiv_i.size(); j++) {
        int val = equiv_i[j];
        if (val == 0 || val == 1) {
          /* Case: reg == const
             Generate: (aLit ==> reg)  if const == 1
                       (aLit ==> !reg) if const == 0
           */
          int a = unroller.freshVar();
          lit aLit = toLit(a);
          lit Lit[1];
          Lit[0] = toLitCond(cnfItp->pVarNums[Aig_ManCi(&*itp, j)->Id], 1);
          if (val == 0)
            unroller.addNamedClause(Lit, Lit + 1, -1, aLit);
          else {
            Lit[0] = lit_neg(Lit[0]);
            unroller.addNamedClause(Lit, Lit + 1, -1, aLit);
          }
          equivToLit[j] = aLit;
        } else if (val != -1) {
          /*
            Case: reg_j = reg_k
            Generate: aLit ==> (reg_j = reg_k)
           */
          // reg_j equals register sign(val) * abs(val)
          int reg = (std::abs(val) / 2) - 1;
          int a = unroller.freshVar();
          lit aLit = toLit(a);
          lit Lit[2];
          Lit[0] = toLit(cnfItp->pVarNums[Aig_ManCi(&*itp, j)->Id]);
          Lit[1] = toLitCond(cnfItp->pVarNums[Aig_ManCi(&*itp, reg)->Id],
                             (val >= 0));
          unroller.addNamedClause(Lit, Lit + 2, -1, aLit);
          Lit[0] = lit_neg(Lit[0]);
          Lit[1] = lit_neg(Lit[1]);
          unroller.addNamedClause(Lit, Lit + 2, -1, aLit);
          equivToLit[j] = aLit;
        }
      }

      unroller.newFrame();
    }
    addPreCond(vc, i);
    if (i < coNum) {
      // adds a copy of Tr and glues it to prev frame
      vc.addTr(unroller);
      unroller.newFrame();

      unsigned nOffset = unroller.freshBlock(cnfItp->nVars);
      ScoppedCnfLift scLift(cnfItp, nOffset);
      unroller.addCnf(&*cnfItp);
      Aig_Obj_t *pCi;
      int j;
      Aig_ManForEachCi(&*itp, pCi, j) {
        unroller.addInput(cnfItp->pVarNums[pCi->Id]);
      }
      unroller.glueOutIn();

      // -- assert !Itp_i
      // -- at this point, Itp_i is already the new version that includes
      // -- all the extra constraints for the rest of the interpolation sequence
      lit Lit = toLitCond(cnfItp->pVarNums[Aig_ManCo(&*itp, i)->Id], 1);
      unroller.addClause(&Lit, &Lit + 1);
    } else {
      vc.addBad(unroller, pBad);
      unroller.pushBadUnit();
    }

    // boost::tribool res = satSolver.solve ();
    tribool res = satSolver.solve(unroller.getAssumps());

    if (res) {
      // AG: this is unexpected output
      VERBOSE(1, vout() << "\nFailed implication at i: " << i << "\n";);
      return false;
    } else if (!res) {
      // AG: result is unsat as expected. Extract unsat core
      VERBOSE(1, vout() << "." << std::flush;);
      // XXX AG: why we would ever do this for i == 0?!
      // AVY_ASSERT(i > 0);
      if (i > 0) {
        int *pCore;
        int coreSz = satSolver.core(&pCore);
        if (coreSz == 0) continue;

        // AG: XXX compute actual core since satSolver.core() returns
        // AG: XXX conflict clause, not the core of assumptions
        IntVector core(pCore, pCore + coreSz);
        for (lit &p : core) p = lit_neg(p);

        IntVector &equivs = equivFrames[i - 1];
        // -- pEq are the extra equalities to be added to Itp
        Aig_Obj_t *pEq = Aig_ManConst1(&*itp);
        for (int j = 0; j < equivs.size(); j++) {
          int eqLit = equivToLit[j];
          bool found = std::any_of(core.begin(), core.end(),
                                   [&](int c) { return c == eqLit; });
          if (found) {
            Aig_Obj_t *t = nullptr;
            // Track the constraints
            int val = equivs[j];
            if (val == 0)
              t = Aig_Not(Aig_ManCi(&*itp, j));
            else if (val == 1)
              t = Aig_ManCi(&*itp, j);
            else if (val != -1) {
              int reg = (std::abs(val) / 2) - 1;
              // Create an AIG expression representing
              // the equivalence
              Aig_Obj_t *p1 = Aig_ManCi(&*itp, j);
              Aig_Obj_t *p2 = Aig_ManCi(&*itp, reg);
              if (val < 0) p2 = Aig_Not(p2);
              t = Aig_And(&*itp, Aig_Or(&*itp, p1, Aig_Not(p2)),
                          Aig_Or(&*itp, Aig_Not(p1), p2));
            }
            if (t) pEq = Aig_And(&*itp, pEq, t);
          }
        }

        // if pEq has any equivalences (i.e., not a constant), add
        // them to the current interpolant
        if (!Aig_ObjIsConst1(Aig_Regular(pEq))) {
          Aig_Obj_t *pItp = Aig_ObjChild0(Aig_ManCo(&*itp, i - 1));
          pItp = Aig_And(&*itp, pItp, pEq);
          Aig_ObjDisconnect(&*itp, Aig_ManCo(&*itp, i - 1));
          Aig_ObjConnect(&*itp, Aig_ManCo(&*itp, i - 1), pItp, nullptr);
          bChanged = true;
        }
      }
    }
  }
  VERBOSE(1, vout() << " Done\n" << std::flush;);
  return true;
}
} // namespace avy

// Explicit instantiation
template avy::tribool
avy::AvyMain::doBmc<avy::ItpGlucose>(unsigned, avy::ItpGlucose &, avy::Muser2 &,
                                     avy::Unroller<avy::ItpGlucose> &,
                                     AigManPtr,
                                     UnsatCoreComputer<avy::ItpGlucose> *);
template avy::tribool
avy::AvyMain::doBmc<avy::ItpMinisat>(unsigned, avy::ItpMinisat &, avy::Muser2 &,
                                     avy::Unroller<avy::ItpMinisat> &,
                                     AigManPtr,
                                     UnsatCoreComputer<avy::ItpMinisat> *);
template avy::tribool
avy::AvyMain::doBmc<avy::ItpCadical>(unsigned, avy::ItpCadical &, avy::Muser2 &,
                                     avy::Unroller<avy::ItpCadical> &,
                                     AigManPtr,
                                     UnsatCoreComputer<avy::ItpCadical> *);