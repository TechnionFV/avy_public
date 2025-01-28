#ifndef _SafetyAigVC_H_
#define _SafetyAigVC_H_

//#include "boost/noncopyable.hpp"

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"
#include "avy/Util/AvyTribool.h"

#include "AigUtils.h"
#include "SafetyVC.h"
#include "aig/saig/saig.h"
#include "sat/cnf/cnf.h"

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
class SafetyAigVC {

  /// the original circuit
  AigManPtr m_Circuit;
  AigManPtr m_MasterTr;
  AigManPtr m_ActualAig;
  /// transition relation part of the circuit
  /// TODO: For now, storing TRs as vector for frame 1 and up (0 is saved
  /// differently) Should change that and figure out what to do to be more
  /// efficient
  std::vector<AigManPtr> m_Tr;
  std::vector<CnfPtr> m_TrCnf;

  /// the bad state
  AigManPtr m_Bad;

  /// Cnf of Bad sates
  CnfPtr m_cnfBad;

  std::vector<Clauses> m_preCond;
  std::vector<Clauses> m_postCond;

  // constant values of each Co/Ci at a given frame
  std::vector<std::vector<tribool>> m_frameVals;
  // equivalences of each Co/Ci at a given frame
  std::vector<std::vector<int>> m_frameEquivs;

  // a map from Aig nodes to SAT variables for each Aig in m_Tr
  std::vector<std::vector<int>> m_AigToSat;

  // Ci in the support of Bad
  std::vector<int> m_BadStartingRoots;
  std::vector<int> m_StartingRoots;

  /// initialize given a circuit
  void init(Aig_Man_t *pCircuit);

  /**
   * Computes an Aig for Tr for the last frame
   */
  void computeNextTr() {
    if (gParams.opt_bmc) {
      AVY_MEASURE_FN;

      std::vector<int> &lastEquiv = m_frameEquivs.back();
      bool modified = false;
      for (int i = 0; i < lastEquiv.size() && !modified; i++)
        if (lastEquiv[i] != -1)
          modified = true;

      if (modified) {
        AigManPtr pNewTr =
            aigPtr(Aig_DupWithCiEquivs(&*m_MasterTr, m_frameEquivs.back()));

        m_frameEquivs.push_back(std::vector<int>());
        Aig_Man_t *pSimpTr = Aig_SatSweep(&*pNewTr, m_frameEquivs.back());
        m_Tr.push_back(aigPtr(pSimpTr));
      } else {
        m_Tr.push_back(m_MasterTr);
        std::vector<int> empty(lastEquiv.size(), -1);
        m_frameEquivs.push_back(empty);
      }
    } else
      m_Tr.push_back(m_MasterTr);
  }

  template <typename S>
  CnfPtr getCnfTr(Unroller<S> &unroller, unsigned nFrame) {
    AVY_MEASURE_FN;
    if (nFrame < m_TrCnf.size()) return m_TrCnf[nFrame];

    AVY_ASSERT(m_TrCnf.size() == nFrame);
    CnfPtr cnfTr = cnfPtr(AvyCnf_Derive(&*m_Tr[nFrame],
                                     Aig_ManRegNum(&*m_Tr[nFrame])));
    m_TrCnf.push_back(cnfTr);
    m_AigToSat.push_back(std::vector<int>((&*cnfTr)->nVars, -1));
    unroller.addNewNodes((&*cnfTr)->nVars);
    // Set variables for INPUTS
    Aig_Obj_t *pObj;
    int i;
    Aig_ManForEachCi(&*m_Tr[nFrame], pObj, i) {
      m_AigToSat.back()[(&*cnfTr)->pVarNums[pObj->Id]] = unroller.freshVar();
      unroller.markAdded(nFrame, (&*cnfTr)->pVarNums[pObj->Id]);
    }

    return cnfTr;
  }

public:
  /// create a VC given from a circuit. Init is implicit.
  SafetyAigVC(Aig_Man_t *pCircuit) {
    m_frameVals.resize(1);
    m_frameVals[0].resize(
        Saig_ManRegNum(pCircuit + (gParams.stick_error ? 1 : 0)), false);
    init(pCircuit);
  }
  template <typename S>
  void markInputsAsAdded(Unroller<S> &unroller)
  {
    // could have not reset them in the first place
    for (int i = 0; i < unroller.frame(); i++) {
      Aig_Obj_t *pObj;
      int j;
      Aig_ManForEachCi(&*m_Tr[i], pObj, j) {
        unroller.markAdded(i, (&*m_TrCnf[i])->pVarNums[pObj->Id]);
      }
    }
  }
  void resetSat() {
    for (int i = 0; i < m_AigToSat.size(); i++)
      m_AigToSat[i].clear();
  }

  AigManPtr getActualAig() { return m_ActualAig; }
  AigManPtr getTr(unsigned nFrame) {
    AVY_ASSERT(nFrame < m_Tr.size());
    return m_Tr[nFrame];
  }
  AigManPtr getBad() { return m_Bad; }

  void resetPreCond() { m_preCond.clear(); }
  void resetPostCond() { m_postCond.clear(); }
  void resetTr() {
    for (CnfPtr &c : m_TrCnf) {
      c.reset();
    }
    m_TrCnf.clear();
    for (AigManPtr &a : m_Tr) {
      a.reset();
    }
    m_Tr.clear();
    resetSat();
  }
  template <typename Iterator>
  void addCondClause(std::vector<Clauses> &clausesByFrame,
                     Iterator bgn, Iterator end,
                     unsigned nFrame, bool fCompl = false) {
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
          if (lit_sign(Lit)) logs() << "-";
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
                            Vec_Int_t *vMap, int nFrame = -1) {
    tribool res = true;
    Clause tmp;
    for (Clause &cls : clauses) {
      tmp.clear();
      for (lit Lit : cls) {
        // map literal based on vMap
        int reg = lit_var(Lit);
        tmp.push_back(toLitCond(Vec_IntEntry(vMap, reg), lit_sign(Lit)));
      }
      res = res && unroller.addClause(&tmp[0], &tmp[0] + tmp.size(), nFrame);
    }
    return res;
  }

  template <typename S> void addTr(Unroller<S> &unroller) {
    unsigned nFrame = unroller.frame();
    while (m_Tr.size() <= nFrame)
      computeNextTr();

    CnfPtr cnfTr = getCnfTr(unroller, nFrame);

    AVY_ASSERT(Vec_IntSize(unroller.getInputs(nFrame)) == 0 &&
               "Unexpected inputs");
    AVY_ASSERT(Vec_IntSize(unroller.getOutputs(nFrame)) == 0 &&
               "Unexpected outputs");
    // AVY_ASSERT (nFrame > 0);

    std::vector<std::vector<int>> roots;
    getSupport(nFrame, roots);
    // -- register frame PIs
    Aig_Obj_t *pObj;
    int i;
    Saig_ManForEachPi(&*m_Tr[nFrame], pObj, i)
      unroller.addPrimaryInput(m_AigToSat[nFrame][cnfTr->pVarNums[pObj->Id]]);

    if (nFrame > 0) {
      // -- register inputs
      Saig_ManForEachLo(&*m_Tr[nFrame], pObj, i)
        unroller.addInput(m_AigToSat[nFrame][cnfTr->pVarNums[pObj->Id]]);

      unroller.setFrozenInputs(nFrame, true);
      /** pre-condition clauses */
      if (nFrame < m_preCond.size())
        addClauses(unroller, m_preCond[nFrame], unroller.getInputs(nFrame));
    }

    // -- add transition relation
    for (int f = 0; f <= nFrame; f++) {
      if (f == 0 && !gParams.opt_bmc) {
        // add clauses for Init
        Aig_Obj_t *pObj;
        int i;
        lit Lits[1];

        Saig_ManForEachLo(&*m_Tr[f], pObj, i) {
          int var = m_AigToSat[f][cnfTr->pVarNums[pObj->Id]];
          if (var > -1) {
            Lits[0] = toLitCond(var, 1);
            unroller.addClause(Lits, Lits + 1);
          }
        }
      }
      // Add needed clauses according to COI
      unroller.addCoiCnf(f, &*(m_Tr[f]), roots[f], m_TrCnf[f], m_AigToSat[f]);
      // -- Update frame outputs
      Vec_Int_t *pOutputs = unroller.getOutputs(f);
      // Vec_IntClear(pOutputs);
      Aig_Obj_t *pObj;
      int i;
      Saig_ManForEachLi(&*m_Tr[f], pObj, i) {
        int var = m_AigToSat[f][m_TrCnf[f]->pVarNums[pObj->Id]];
        if (Vec_IntSize(pOutputs) > i) {
          if (var > -1)
            Vec_IntWriteEntry(pOutputs, i, var);
        } else {
          Vec_IntPush(pOutputs, var);
        }
      }
      // Update the glue variables
      if (f < nFrame && f >= 0) {
        unroller.glueOutIn(f + 1);
      }
      if (f > 0 && f < m_preCond.size()) {
        addClauses(unroller, m_preCond[f], unroller.getInputs(f), f);
      }
    }
    /** post-condition clauses */
    if (unroller.frame() < m_postCond.size())
      addClauses(unroller, m_postCond[nFrame], unroller.getOutputs(nFrame));
  }

  template <typename S>
  void addMissingTrParts(Unroller<S> &unroller, unsigned nFrame) {
    AVY_ASSERT(nFrame < unroller.frame());

    CnfPtr cnfTr = getCnfTr(unroller, nFrame);

    AVY_ASSERT((Vec_IntSize(unroller.getInputs(nFrame)) > 0) &&
               "Unexpected absence of inputs");
    AVY_ASSERT(Vec_IntSize(unroller.getOutputs(nFrame)) > 0 &&
               "Unexpected absence of outputs");

    //        unroller.setFrozenInputs(nFrame, true);
    /** pre-condition clauses */
    if (nFrame < m_preCond.size())
      addClauses(unroller, m_preCond[nFrame], unroller.getInputs(nFrame));

    std::vector<std::vector<int>> roots;
    getSupport(nFrame, roots);
    // -- add transition relation
    for (int f = 0; f <= nFrame; f++) {
      // Add needed clauses according to COI
      unroller.addCoiCnf(f, &*(m_Tr[f]), roots[f], m_TrCnf[f], m_AigToSat[f]);
      // -- Update frame outputs
      Vec_Int_t *pOutputs = unroller.getOutputs(f);
      // Vec_IntClear(pOutputs);
      Aig_Obj_t *pObj;
      int i;
      Saig_ManForEachLi(&*m_Tr[f], pObj, i) {
        int var = m_AigToSat[f][m_TrCnf[f]->pVarNums[pObj->Id]];
        AVY_ASSERT(var == -1 || Vec_IntSize(pOutputs) > i);
        if (var > -1)
          Vec_IntWriteEntry(pOutputs, i, var);
        // if (var > -1) printf("i=%d, var=%d\n", i, var);
        // Vec_IntPush(pOutputs, var);
      }

      // Update the glue variables
      if (f < nFrame && f >= 0) {
        unroller.glueOutIn(f + 1);
      }
      if (f > 0 && f < m_preCond.size()) {
        addClauses(unroller, m_preCond[f], unroller.getInputs(f), f);
      }
    }

    /** post-condition clauses */
    if (unroller.frame() < m_postCond.size())
      addClauses(unroller, m_postCond[nFrame], unroller.getOutputs(nFrame));
  }
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
      if (i < Saig_ManPiNum(&*m_MasterTr)) {
        unroller.addPrimaryInput(pCnfBad->pVarNums[pObj->Id]);
      } else {
        unroller.addInput(pCnfBad->pVarNums[pObj->Id]);
      }
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

  const std::vector<tribool> &getLatchesValues(unsigned nFrame) const {
    AVY_ASSERT(m_frameVals.size() > nFrame);
    return m_frameVals[nFrame];
  }

  std::vector<std::vector<int>> &getFrameEquivs() { return m_frameEquivs; }


  void getSupport(unsigned nFrame, std::vector<std::vector<int>> &roots);

  /**
   * Sets m_StartingRoots with Ci that drive Co 0 in the input pAig
   * If the input pAig is nullptr, sets m_StartingRoots to roots of BAD
   */
  void computerStartingRoots(AigManPtr pAig = nullptr) {
    if (pAig == nullptr)
      m_StartingRoots = m_BadStartingRoots;
    else {
      // -- compute support of Po 0 of the input Aig
      std::vector<int> startingRoots(1, 0);
      Aig_GetSupport(&*pAig, startingRoots, m_StartingRoots);
    }
  }
};
} // namespace avy

#endif /* _SafetyAigVC_H_ */
