#include "ItpValidator.h"
#include "SafetyVC2.h"

using namespace avy;
namespace {
void addPreCond(SafetyVC2 &vc, AvyTrace &TraceMan, int vcLevel, int frameLevel) {
  TraceMan.getLemmasAtFrame(frameLevel,vc.modifyPreCond(vcLevel));
}
}

namespace avy {
template <typename SatSolver>
bool ItpValidator<SatSolver>::operator()(Aig_Man_t *itp, Aig_Man_t *Tr, AvyTrace& TraceMan, int lemmaLevel) {
  VERBOSE(1, vout() << "Validating ITP: ";);
  CnfPtr cnfItp = cnfPtr(AvyCnf_Derive(&*itp, Aig_ManCoNum(&*itp)));

  unsigned coNum = Aig_ManCoNum(&*itp);
  VERBOSE(1, vout() << "CoNum: " << coNum << "\n";);
  for (unsigned int i = 0; i <= coNum; ++i) {
    SatSolver satSolver(2, 5000);
    Unroller<SatSolver> unroller(satSolver);
    SafetyVC2 vc(Tr, m_propagate,false,nullptr);
    // -- fast forward the unroller and the VC to the right frame
    while (i >= 2 && unroller.frame() < i - 1)
      unroller.newFrame();

    if (i > 0) {
      unsigned nOffset = unroller.freshBlock(cnfItp->nVars);
      ScoppedCnfLift scLift(cnfItp, nOffset);
      unroller.addCnf(&*cnfItp);

      // -- assert Itp_{i-1}
      lit Lit = toLit(cnfItp->pVarNums[Aig_ManCo(&*itp, i - 1)->Id]);
      satSolver.addClause(&Lit, &Lit + 1);

      // -- register outputs
      Aig_Obj_t *pCi;
      int j;
      Aig_ManForEachCi(&*itp, pCi, j)
        unroller.addOutput(cnfItp->pVarNums[pCi->Id]);

      unroller.newFrame();
    }
    /*
     * For each interpolant, validate sequence interpolant
     * using only the lemmas that were used to derive it.
     */
    int level = lemmaLevel >=i ? lemmaLevel:i;
    //Does not treat init as special. Init will have all the preconditions as
    //all the frames instead of just latches=0
    //since latches=0 is the strongest amongst them,I don't think it matters.
    addPreCond(vc,TraceMan,i,level);
    if (i < coNum) {
      vc.addTr(unroller);
      unroller.newFrame();

      unsigned nOffset = unroller.freshBlock(cnfItp->nVars);
      ScoppedCnfLift scLift(cnfItp, nOffset);
      unroller.addCnf(&*cnfItp);
      Aig_Obj_t *pCi;
      int j;
      Aig_ManForEachCi(&*itp, pCi, j)
        unroller.addInput(cnfItp->pVarNums[pCi->Id]);
      unroller.glueOutIn();

      // -- assert !Itp_i
      lit Lit = toLitCond(cnfItp->pVarNums[Aig_ManCo(&*itp, i)->Id], 1);
      unroller.addClause(&Lit, &Lit + 1);
    } else {
      vc.addBad(unroller);
      unroller.pushBadUnit();
    }

    if (satSolver.solve(unroller.getAssumps()) != false) {
      VERBOSE(1, vout() << "\nFailed validation at i: " << i << "\n";);
      return false;
    } else
      VERBOSE(1, vout() << "." << std::flush;);
  }

  VERBOSE(1, vout() << " Done\n" << std::flush;);
  return true;
}
}

template class avy::ItpValidator<avy::Glucose>;
