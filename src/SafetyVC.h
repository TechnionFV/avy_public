#ifndef _SAFETYVC_H_
#define _SAFETYVC_H_

//#include "boost/noncopyable.hpp"

#include "avy/Util/AvyDebug.h"
#include "avy/Util/AvyTribool.h"
#include "avy/Util/Global.h"

#include "AigUtils.h"
#include "aig/saig/saig.h"

#include "CnfUtils.h"
#include "Unroller.h"
#include "boost/range.hpp"

#include <vector>
namespace avy {
using namespace avy::abc;

/**
 * Safety Verification Condition: encodes Init & Tr^i & Bad
 * Tr is given by an Aig with a single Po
 * Bad is the driver of the Po of Tr
 * Init is zero for all registers
 */
class SafetyVC {

  /// the original circuit
  AigManPtr m_Circuit;
  /// transition relation part of the circuit
  AigManPtr m_Tr;
  /// the bad state
  AigManPtr m_Bad;

  /// Tr of the 0 frame
  AigManPtr m_Tr0;

  /// Cnf of Tr
  CnfPtr m_cnfTr;

  /// Cnf of Bad sates
  CnfPtr m_cnfBad;

  /// Cnf of Tr0
  CnfPtr m_cnfTr0;

  AigManPtr m_ActualCirc;

  typedef std::vector<lit> Clause;
  typedef std::vector<Clause> Clauses;
  std::vector<Clauses> m_preCond;
  std::vector<Clauses> m_postCond;

  /// initialize given a circuit
  void init(Aig_Man_t *pCircuit);

public:
  /// create a VC given from a circuit. Init is implicit.
  SafetyVC(Aig_Man_t *pCircuit) { init(pCircuit); }

  AigManPtr getTr() { return m_Tr; }
  AigManPtr getBad() { return m_Bad; }
  AigManPtr getActual() { return m_ActualCirc; }

  void resetPreCond() { m_preCond.clear(); }
  void resetPostCond() { m_postCond.clear(); }

  template <typename Iterator>
  void addCondClause(std::vector<Clauses> &clausesByFrame, Iterator bgn,
                     Iterator end, unsigned nFrame, bool fCompl = false) {
    AVY_ASSERT(nFrame > 0);

    LOG("learnt", logs() << "CLS at " << nFrame << ": ";
        for (lit Lit : boost::make_iterator_range(bgn, end)) {
          if (Lit == -1)
            continue;
          if (lit_sign(Lit))
            logs() << "-";
          logs() << lit_var(Lit) << " ";
        }
        logs() << "\n";);

    clausesByFrame.resize(nFrame + 1);
    Clauses &clauses = clausesByFrame[nFrame];
    clauses.resize(clauses.size() + 1);
    for (Iterator it = bgn; it != end; ++it) {
      if (*it == -1)
        continue;
      lit Lit = *it;
      if (fCompl)
        Lit = lit_neg(Lit);
      clauses.back().push_back(Lit);
    }

    LOG("learnt2", logs() << "CLS at " << nFrame << ": ";
        for (lit Lit : clauses.back()) {
          if (lit_sign(Lit))
            logs() << "-";
          logs() << lit_var(Lit) << " ";
        }
        logs() << "\n";);
  }

  /**
     Add a (optinally negated) clause to the pre-condition at a given frame
   */
  template <typename Iterator>
  void addPreCondClause(Iterator bgn, Iterator end, unsigned nFrame,
                        bool fCompl = false) {
    AVY_ASSERT(nFrame > 0);
    addCondClause(m_preCond, bgn, end, nFrame, fCompl);
  }

  /**
   * Add a (optionally negated) clause to the post-condition at a given frame
   */
  template <typename Iterator>
  void addPostCondClause(Iterator bgn, Iterator end, unsigned nFrame,
                         bool fCompl = false) {
    addCondClause(m_postCond, bgn, end, nFrame, fCompl);
  }

  template <typename S>
  tribool addClauses(Unroller<S> &unroller, Clauses &clauses,
                            Vec_Int_t *vMap) {
    tribool res = true;
    Clause tmp;
    for (Clause &cls : clauses) {
      tmp.clear();
      for (lit Lit : cls) {
        // map literal based on vMap
        int reg = lit_var(Lit);
        tmp.push_back(toLitCond(Vec_IntEntry(vMap, reg), lit_sign(Lit)));
      }
      res = res && unroller.addClause(&tmp[0], &tmp[0] + tmp.size());
    }
    return res;
  }

  template <typename S> void addTr(Unroller<S> &unroller) {
    unsigned nFrame = unroller.frame();
    if (nFrame == 0)
      addTr0(unroller);
    else
      addTrN(unroller);

    /** post-condition clauses */
    if (unroller.frame() < m_postCond.size())
      addClauses(unroller, m_postCond[nFrame], unroller.getOutputs(nFrame));
  }

private:
  template <typename S> void addTr0(Unroller<S> &unroller) {
    unsigned nOff = unroller.freshBlock(m_cnfTr0->nVars);
    ScoppedCnfLift scLift(m_cnfTr0, nOff);

    unsigned nFrame = unroller.frame();

    AVY_ASSERT(Vec_IntSize(unroller.getInputs(nFrame)) == 0 &&
               "Unexpected inputs");
    AVY_ASSERT(Vec_IntSize(unroller.getOutputs(nFrame)) == 0 &&
               "Unexpected outputs");
    AVY_ASSERT(nFrame == 0);

    // add clauses for Init
    Aig_Obj_t *pObj;
    int i;
    lit Lits[1];

    Saig_ManForEachLo(&*m_Tr0, pObj, i) {
      Lits[0] = toLitCond(m_cnfTr0->pVarNums[pObj->Id], 1);
      unroller.addClause(Lits, Lits + 1);
    }

    unroller.addCnf(&*m_cnfTr0);

    // -- register frame PIs
    Saig_ManForEachPi(&*m_Tr0, pObj, i)
        unroller.addPrimaryInput(m_cnfTr0->pVarNums[pObj->Id]);

    // -- register frame outputs
    Saig_ManForEachLi(&*m_Tr0, pObj, i)
        unroller.addOutput(m_cnfTr0->pVarNums[pObj->Id]);
  }

  template <typename S> void addTrN(Unroller<S> &unroller) {
    unsigned nOff = unroller.freshBlock(m_cnfTr->nVars);
    ScoppedCnfLift scLift(m_cnfTr, nOff);

    unsigned nFrame = unroller.frame();

    AVY_ASSERT(Vec_IntSize(unroller.getInputs(nFrame)) == 0 &&
               "Unexpected inputs");
    AVY_ASSERT(Vec_IntSize(unroller.getOutputs(nFrame)) == 0 &&
               "Unexpected outputs");
    AVY_ASSERT(nFrame > 0);

    // -- register frame PIs
    Aig_Obj_t *pObj;
    int i;
    Saig_ManForEachPi(&*m_Tr, pObj, i)
        unroller.addPrimaryInput(m_cnfTr->pVarNums[pObj->Id]);

    // -- register inputs
    Saig_ManForEachLo(&*m_Tr, pObj, i)
        unroller.addInput(m_cnfTr->pVarNums[pObj->Id]);

    // glue new In to old Out
    unroller.glueOutIn();

    /** pre-condition clauses */
    if (nFrame < m_preCond.size())
      addClauses(unroller, m_preCond[nFrame], unroller.getInputs(nFrame));

    // -- add transition relation
    unroller.addCnf(&*m_cnfTr);

    // -- register frame outputs
    Saig_ManForEachLi(&*m_Tr, pObj, i)
        unroller.addOutput(m_cnfTr->pVarNums[pObj->Id]);
  }

public:
  template <typename S>
  void addBad(Unroller<S> &unroller, AigManPtr pBad = NULL) {
    CnfPtr pCnfBad = m_cnfBad;
    if (pBad == NULL)
      pBad = m_Bad;
    else
      pCnfBad = cnfPtr(AvyCnf_Derive(&*pBad, Aig_ManCoNum(&*pBad)));

    unsigned nOff = unroller.freshBlock(pCnfBad->nVars);
    ScoppedCnfLift scLift(pCnfBad, nOff);

    unsigned nFrame = unroller.frame();

    AVY_ASSERT(Vec_IntSize(unroller.getInputs(nFrame)) == 0 &&
               "Unexpected inputs");
    AVY_ASSERT(Vec_IntSize(unroller.getOutputs(nFrame)) == 0 &&
               "Unexpected outputs");

    // -- register inputs
    Aig_Obj_t *pObj;
    int i;
    Aig_ManForEachCi(&*pBad, pObj, i) {
      // -- skip Ci that corresponds to Pi of Tr
      if (i < Saig_ManPiNum(&*m_Tr0))
        unroller.addPrimaryInput(pCnfBad->pVarNums[pObj->Id]);
      else
        unroller.addInput(pCnfBad->pVarNums[pObj->Id]);
    }

    // -- glue
    unroller.glueOutIn();

    /** pre-condition clauses */
    if (nFrame < m_preCond.size())
      addClauses(unroller, m_preCond[nFrame], unroller.getInputs(nFrame));

    // -- add bad states
    unroller.addCnf(&*pCnfBad);

    // -- assert bad output
    lit Lit = toLit(pCnfBad->pVarNums[Aig_ManCo(&*pBad, 0)->Id]);
    unroller.setBadLit(Lit);
  }
};
} // namespace avy

#endif /* _SAFETYVC_H_ */
