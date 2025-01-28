#pragma once
#include "SafetyVC2.h"
#include "Unroller.h"
#include "boost/dynamic_bitset.hpp"
#include "boost/range/algorithm/copy.hpp"
#include <string>

#include "AvyTypes.h" //IntVector
#include "ItpGlucose.h"
#include "ItpMinisat.h"
#include "ItpCadical.h"
#include "Muser2.h"

#include "Pdr.h"
#include "Glucose.h"

namespace avy {
  /*
   * A class for computing the support of a lemma
   */
  template <typename SatSolver = Glucose>
  class LemmaSupport {

  /// AvyTrace
  AvyTrace m_TraceMan;

  /// The AIG
  Aig_Man_t * m_Aig;

public:
  LemmaSupport(Aig_Man_t *Tr) : m_Aig(Tr) {}

  IntVector operator()(AvyTrace &trace, Pdr_Set_t *pCube, int level) {
    /// For now, assume level is greater than 1
    AVY_ASSERT( level > 1 );
    SatSolver satSolver(2, 5000);
    Muser2 muser(2);
    Unroller<SatSolver> unroller(satSolver, &muser, true);
    SafetyVC2 vc(m_Aig, false,true, true, nullptr);

    // -- Put the lemmas of level-1 at the first frame of our temporary VC
    trace.getLemmasAtFrame(level-1, vc.modifyPreCond(1));

    // -- setup the unroller like we want it:
    // -- 2 frames, cannot use only 1 frame because of init
    // -- register frame outputs. We are skipping the addition of TR for
    // -- first frame as it is not required. This requires us to register
    // -- the outputs of that frame manually.
    int i;
    Aig_Obj_t *pObj;
    Saig_ManForEachLi(m_Aig, pObj, i) {
      unroller.addOutput(unroller.freshVar());
    }
    unroller.newFrame();
    vc.addTr(unroller);
    unroller.newFrame();

    // -- Two frames for Tr, one for Bad
    AVY_ASSERT(unroller.frames() == 3);

    // -- Create the BAD states
    AigManPtr pBad = aigPtr(cubeToAig(&*vc.getActual(), pCube));

    // -- Add BAD to VC and make sure it's in the unroller and Muser.
    vc.addBad(unroller, pBad);
    lit badLit = unroller.getBadLit();
    unroller.addAssump(badLit);
    muser.addClause(&badLit, &badLit+1, badLit);

    // -- Sanity check - see that we get UNSAT results
    tribool res = satSolver.solve(unroller.getAssumps());
    int *c = nullptr;
    int s = satSolver.core(&c);

    AVY_ASSERT(res == false);

    IntVector core(muser.getUnsatCore());

    return core;

  }

  private:
    Aig_Man_t* cubeToAig(Aig_Man_t *pActualAig, Pdr_Set_t *pCube) {
      Aig_Man_t *pCubeAig = Aig_ManStart(m_Aig->nRegs);
      for (int i = 0; i < m_Aig->nRegs; i++) Aig_ObjCreateCi(pCubeAig);

      Aig_Obj_t *pRes = Aig_ManConst1(pCubeAig);

      for (int i = 0; i < pCube->nLits; ++i) {
        if (pCube->Lits[i] == -1)
          continue;

        Aig_Obj_t *pObj;

        pObj = Aig_ManCi(pCubeAig, lit_var(pCube->Lits[i]));
        pObj = Aig_NotCond(pObj, lit_sign(pCube->Lits[i]));
        pRes = Aig_And(pCubeAig, pRes, pObj);
      }

      Aig_ObjCreateCo(pCubeAig, pRes);
      AigManPtr newTr =
              aigPtr(Aig_ManReplacePo(pActualAig, &*pCubeAig, false));
      newTr = aigPtr(Aig_ManGiaDup(&*newTr));
      Aig_Man_t *pTemp = (Aig_ManDupSinglePo(&*newTr, 0, false));
      Aig_ManRebuild(&pTemp);

      return pTemp;
  }
};
}; // namespace avy
