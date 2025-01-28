#pragma once

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "AigUtils.h"
#include "CnfUtils.h"
#include "Unroller.h"
#include "AvyTrace.h"
#include "aig/saig/saig.h"
#include "boost/range.hpp"
#include "AvyTypes.h" //litvector, Clauses, Clause, Lemmas
#include <vector>

namespace avy {

/**
 * Safety Verification Condition: encodes Init & Tr^i & Bad
 * Tr is given by an Aig with a single Po
 * Bad is the driver of the Po of Tr
 * Init is zero for all registers
 */
class SafetyVC2 {
  class FrameInfo {
    // -- number of this frame
    unsigned m_frameNum;

    /// AIG of the Tr
    AigManPtr m_Tr;
    /// (Shifted) CNF of the Tr
    CnfPtr m_cnfTr;

    /// index of the first CNF variable for the Tr
    unsigned m_cnfVar;

    /// pre-condition clauses (over input variables)
    Lemmas m_preCond;
    /// post-condition clauses (over output variables)
    Lemmas m_postCond;

    /// equivalence relation on Co.  A Co is mapped to 0/1 for
    /// false/true, to another Co, or to -1 if it cannot be simplified
    IntVector m_outEquivs;

    /// Mark which nodes in m_Tr are committed to the sat-solver
    boost::dynamic_bitset<> m_committed;

    void setCnfVar(unsigned v) { m_cnfVar = v; }

  public:
    FrameInfo(unsigned frameNum) : m_frameNum(frameNum) {}

    IntVector &getOutputEquivs() { return m_outEquivs; }

    void addPreCondClause(AvyLemma* lptr) {
      m_preCond.push_back(lptr);
    }
    void resetPreCond() { m_preCond.clear(); }
    const Lemmas &getPreCond() const { return m_preCond; }
    //modify preconditions
    Lemmas & modifyPreCond() { return m_preCond; }

    void addPostCondClause(AvyLemma* lptr) {
      m_postCond.push_back(lptr);
    }
    void resetPostCond() { m_postCond.clear(); }
    const Lemmas &getPostCond() const { return m_postCond; }

    unsigned cnfVar() const { return m_cnfVar; }

    unsigned frameNum() const { return m_frameNum; }
    AigManPtr tr() { return m_Tr; }
    void setTr(AigManPtr v) { m_Tr = v; }
    bool hasTr() const { return m_Tr.get(); }

    CnfPtr cnf() { return m_cnfTr; }
    void setCnf(CnfPtr v, unsigned minVar) {
      m_cnfTr = v;
      setCnfVar(minVar);
    }
    bool hasCnf() const { return m_cnfTr.get(); }

    bool isCommittedReg(int reg) const {
      if (!hasTr())
        return false;
      if (reg >= Aig_ManCoNum(&*m_Tr))
        return false;

      Aig_Obj_t *pObj = Aig_ManCo(&*m_Tr, reg);
      return isCommittedObj(pObj);
    }

    bool isCommittedObj(Aig_Obj_t *pObj) const {
      if (!hasTr())
        return false;

      int iObj = Aig_ObjId(pObj);
      if (iObj < 0 || m_committed.size() <= iObj)
        return false;
      return m_committed[iObj];
    }

    void commitObj(Aig_Obj_t *pObj) {
      int iObj = Aig_ObjId(pObj);
      if (m_committed.size() <= iObj)
        m_committed.resize(iObj + 1, 0);
      m_committed[iObj] = 1;
    }
  };

  AvyTrace* m_TraceMan;
  /// the original circuit
  AigManPtr m_Circuit;
  /// transition relation part of the circuit
  AigManPtr m_Tr;
  /// the bad state
  AigManPtr m_Bad;

  /// Tr of the 0 frame
  AigManPtr m_Tr0;

  /// Cnf of Bad sates
  CnfPtr m_cnfBad;

  AigManPtr m_ActualCirc;

  typedef std::vector<std::unique_ptr<FrameInfo>> FrameInfoVec;
  FrameInfoVec m_frames;

  /// Optimize transition relation with sat-sweeping
  bool m_propagate;

  /// add assumption literals to init and precondition lemmas
  bool m_lemmaAbs;

  /// initialize given a circuit
  void init(Aig_Man_t *pCircuit);

  void newFrame() {
    unsigned id = m_frames.size();
    m_frames.push_back(std::unique_ptr<FrameInfo>(new FrameInfo(id)));
  }

  FrameInfo *frame(unsigned nFrame) {
    while (m_frames.size() <= nFrame)
      newFrame();
    return m_frames.at(nFrame).get();
  }

public:
  /// setting and getting preconditions
  /// since we have one global db, different VC objects share
  /// pointers to the lemmas
  const Lemmas & getPreCond(unsigned nFrame)
  {
      return  frame(nFrame)->getPreCond();
  }
  Lemmas & modifyPreCond(unsigned nFrame)
  {
      frame(nFrame)->resetPreCond();
      return frame(nFrame)->modifyPreCond();
  }
  /// create a VC given from a circuit
  SafetyVC2(Aig_Man_t *pCircuit, bool fPropagate,bool flemmaAbs,AvyTrace* db);

  AigManPtr getTr() { return m_Tr; }
  AigManPtr getBad() { return m_Bad; }
  AigManPtr getActual() { return m_ActualCirc; }
  unsigned getSize() { return m_frames.size(); }

  void resetPreCond() {
    for (auto &fr : m_frames) {
      //do not reset the first frame
      //this supports incr mode since precond for frame 0 is
      //added only when the unroller sets up frame 0.
      if (fr->frameNum() == 0)
        continue;
      fr->resetPreCond();
    }
  }
  void resetPostCond() {
    for (auto &fr : m_frames)
      fr->resetPostCond();
  }

  /**
     Add lemmas  to the pre-condition at all frames <= nFrame
   */
  void addPreCondClause(AvyLemma* lptr,unsigned nFrame) {
    for (int j = std::min((unsigned)1,nFrame); j <= nFrame; ++j) {
      frame(j)->addPreCondClause(lptr);
    }
  }

  /**
   * Add a (optionally negated) clause to the post-condition at a given frame
   */
  void addPostCondClause(AvyLemma * lptr,unsigned nFrame) {
    frame(nFrame)->addPostCondClause(lptr);
  }

  /**
   * Add clauses with an optional assumption literal
   * The assumption literal can either be the bad literal 
   * or a new assumption literal from the unroller
   */
  template <typename S>
  tribool addClauses(Unroller<S> &unroller, const Lemmas & lemmas,
                            Vec_Int_t *vMap, int nFrame,bool withAssumps=false) {
    tribool res = true;
    Clause tmp;
    for (const AvyLemma * lemma : lemmas) {
      tmp.clear();
      for (lit Lit : lemma->getLiterals()) {
        // map literal based on vMap
        int reg = lit_var(Lit);
        tmp.push_back(toLitCond(Vec_IntEntry(vMap, reg), lit_sign(Lit)));
      }
      if(withAssumps)
      {
        lit a = unroller.getAssumpLit(lemma->getId(),nFrame,lemma->getFrame());
        res = res && unroller.addNamedClause(&tmp[0], &tmp[0] + tmp.size(), nFrame,a);
      }
      else
      res = res && unroller.addClause(&tmp[0], &tmp[0] + tmp.size(), nFrame);
    }
    return res;
  }

  /**
      Sets up the current frame of the unroller.
      Registers inputs/outputs, adds glue clauses, etc.
      Everything, except for asserting the logic of the Tr.
   */
  template <typename S> void setupFrame(Unroller<S> &unroller, bool noResetPi = false) {
    unsigned nFrame = unroller.frame();

    if (nFrame == 0 && !noResetPi)
      setupFrame0(unroller, !m_propagate);
    else
      setupFrameN(unroller);
    unroller.setFrozenInputs(nFrame, true);
  }

  /**
     Add logic of Tr to the current frame of the unroller.
     Does the necessary setup and adds full logic of the Tr
  */
  template <typename S> void addTr(Unroller<S> &unroller, bool noResetPi = false) {
    setupFrame(unroller, noResetPi);
    addTrLogic(unroller);
    addCondLogic(unroller);
  }

  void getUncommitedInFrame(unsigned f, std::vector<int>& vars) {
    FrameInfo *frameInfo = frame(f);
    Aig_Man_t *pAig = frameInfo->tr().get();
    int j;
    Aig_Obj_t *pObj;
    Cnf_Dat_t *pCnf = &*frameInfo->cnf();
    Aig_ManForEachObj(pAig, pObj, j) {
      if (!frameInfo->isCommittedObj(pObj)) {
          if (!Aig_ObjIsCo(pObj) && !Aig_ObjIsAnd(pObj)) continue;
          int nClas = pCnf->pObj2Count[pObj->Id];
          int iCla = pCnf->pObj2Clause[pObj->Id];
          for (int i = 0; i < nClas; i++) {
            int *pClauseThis = pCnf->pClauses[iCla + i];
            int *pClauseNext = pCnf->pClauses[iCla + i + 1];
            while (pClauseThis != pClauseNext)
              vars.push_back(lit_var(*pClauseThis++));
          }
      }
    }
  }

protected:
  /// Setup frame 0 in the unroller
  /// Initialize FrameInfo, inputs, outputs, and initial condition
  template <typename S>
  void setupFrame0(Unroller<S> &unroller, bool fWithInit = true) {
    unsigned nFrame = unroller.frame();
    AVY_ASSERT(nFrame == 0);
    FrameInfo *pFrame = frame(nFrame);
    AVY_ASSERT(pFrame);
    FrameInfo &frame = *pFrame;

    // -- compute and set Tr for the frame
    AVY_ASSERT(!frame.hasTr());
    mkFrameTr0();
    AVY_ASSERT(frame.hasTr());

    // -- derive CNF
    CnfPtr cnfTr0 =
        cnfPtr(AvyCnf_Derive(&*frame.tr(), Aig_ManRegNum(&*frame.tr())));
    // -- allocate variables in sat-solver
    unsigned nOff = unroller.freshBlock(cnfTr0->nVars);
    // -- shift CNF to sat-solver variables
    Cnf_DataLift(&*cnfTr0, nOff);
    // -- store CNF
    frame.setCnf(cnfTr0, nOff);

    Aig_Obj_t *pObj;
    int i;

    if(fWithInit)
    {
      //treating init as normal inputs
      Saig_ManForEachLo(&*pFrame->tr(), pObj, i) {
        unroller.addInput(pFrame->cnf()->pVarNums[pObj->Id]);
      }
      //add init as preconditions of frame 0
      std::vector<IntVector> clauses = getInit();
      Clause tmp;
      for(IntVector c : clauses)
      {
        if(m_TraceMan) {
          AvyLemma &lemma = m_TraceMan->mkLemma(c, 0, false);
          addPreCondClause(&lemma, 0);
        } else
        {
          //If there is no lemma database, add init clauses
          //directly to the sat solver
          tmp.clear();
          for (lit Lit : c) {
            // map literal based on vMap
            int reg = lit_var(Lit);
            tmp.push_back(toLitCond(Vec_IntEntry(unroller.getInputs(0), reg), lit_sign(Lit)));
          }
          unroller.addClause(&*tmp.begin(),&*tmp.end(),0);
        }
      }
    }

    // -- register frame PIs
    Saig_ManForEachPi(&*frame.tr(), pObj, i) {
      unroller.addPrimaryInput(cnfTr0->pVarNums[pObj->Id]);
    }

    // -- register frame outputs
    Saig_ManForEachLi(&*frame.tr(), pObj, i) {
      unroller.addOutput(cnfTr0->pVarNums[pObj->Id]);
    }
  }

  void mkFrameTr0() {
    FrameInfo *pFrame = frame(0);
    if (!m_propagate) {
      pFrame->setTr(m_Tr0);
      return;
    }

    // initially, all registers are equivalent to false/0
    IntVector initState(Saig_ManRegNum(&*m_Tr0), 0);
    // duplicate pTr while replacing all Ci with false
    AigManPtr pNewTr = aigPtr(Aig_DupWithCiEquivs(&*m_Tr0, initState));
    // compute equivalences on output by sat-sweeping
    IntVector &equivs = pFrame->getOutputEquivs();
    AVY_ASSERT(equivs.empty());
    AigManPtr pSimpTr = aigPtr(Aig_SatSweep(&*pNewTr, equivs));
    // clear equivs if there is nothing
    if (std::all_of(equivs.begin(), equivs.end(),
                    [](int i) { return i == -1; }))
      equivs.clear();

    pFrame->setTr(pSimpTr);
  }

  void mkFrameTrN(unsigned nFrame) {
    AVY_ASSERT(nFrame > 0);
    // either FrameInfo does not exist, or it has no Tr
    AVY_ASSERT(m_frames.size() <= nFrame || !m_frames.at(nFrame)->hasTr());
    FrameInfo *pFrame = frame(nFrame);

    // -- simple case, all Tr in every step
    if (!m_propagate) {
      // -- use master Tr
      pFrame->setTr(m_Tr);
      return;
    }

    // compute next step of Tr by propagating output equivalences from
    // the previous frame

    FrameInfo *pPrevFrame = frame(nFrame - 1);

    if (!pPrevFrame->getOutputEquivs().empty()) {
      // -- simplify Tr using equivalences from previous frame
      AigManPtr pNewTr =
          aigPtr(Aig_DupWithCiEquivs(&*m_Tr, pPrevFrame->getOutputEquivs()));

      IntVector &equivs = pFrame->getOutputEquivs();
      AVY_ASSERT(equivs.empty());

      // -- compute equivalences of newTr by sat-sweeping (updated
      // -- equivalences as a side-effect)
      Aig_Man_t *pSimpTr = Aig_SatSweep(&*pNewTr, equivs);

      // reset empty equivalences
      if (std::all_of(equivs.begin(), equivs.end(),
                      [](int i) { return i == -1; }))
        equivs.clear();

      // -- done with Tr computation
      pFrame->setTr(aigPtr(pSimpTr));
    } else {
      pFrame->setTr(m_Tr);
    }
  }

  /// Setup frame N in the unroller
  /// Initialize FrameInfo, inputs, outputs, and glue prev outputs to inputs
  template <typename S> void setupFrameN(Unroller<S> &unroller) {

    unsigned nFrame = unroller.frame();
    AVY_ASSERT(nFrame > 0);
    FrameInfo *pFrame = frame(nFrame);
    AVY_ASSERT(pFrame);
    FrameInfo &frame = *pFrame;

    AVY_ASSERT(!frame.hasTr());
    mkFrameTrN(nFrame);
    AVY_ASSERT(frame.hasTr());

    // -- derive CNF
    CnfPtr cnfTr =
        cnfPtr(AvyCnf_Derive(&*frame.tr(), Aig_ManRegNum(&*frame.tr())));
    // -- allocate variables in sat-solver
    unsigned nOff = unroller.freshBlock(cnfTr->nVars);
    // -- shift CNF to sat-solver variables
    Cnf_DataLift(&*cnfTr, nOff);
    // -- store CNF
    frame.setCnf(cnfTr, nOff);

    Aig_Obj_t *pObj;
    int i;

    // -- register frame PIs
    Saig_ManForEachPi(&*frame.tr(), pObj, i) {
      unroller.addPrimaryInput(cnfTr->pVarNums[pObj->Id]);
    }

    // -- register inputs
    Saig_ManForEachLo(&*frame.tr(), pObj, i) {
      unroller.addInput(cnfTr->pVarNums[pObj->Id]);
    }

    // -- register frame outputs
    Saig_ManForEachLi(&*frame.tr(), pObj, i) {
      unroller.addOutput(cnfTr->pVarNums[pObj->Id]);
    }

    // glue old Out to new In
    unroller.glueOutIn();
  }

  /// Add logic for the transition relation at the given frame
  template <typename S> void addTrLogic(Unroller<S> &unroller) {
    FrameInfo *pFrame = frame(unroller.frame());
    unroller.addCnf(&*pFrame->cnf());
  }

  /// Add logic for the transition relation of the given frame for given set of
  /// output registers
  template <typename S>
  void addTrLogic(Unroller<S> &unroller, FrameInfo &frame,
                  const IntVector &regs) {
    AVY_ASSERT(std::all_of(regs.begin(), regs.end(), [&](int i) {
      return i < Aig_ManCoNum(&*frame.tr());
    }));

    Aig_Man_t *pTr = &*frame.tr();

    for (auto reg : regs) {
      if (frame.isCommittedReg(reg))
        continue;

      Aig_Obj_t *pObj = Aig_ManCo(pTr, reg);
      if (Aig_ObjFanin0(pObj) == Aig_ManConst0(pTr))
        continue;

      addTrLogicForObj(unroller, frame, pObj);
    }
  }

  template <typename S>
  void addTrLogicForObj(Unroller<S> &unroller, FrameInfo &frame,
                        Aig_Obj_t *pObj) {
    AVY_ASSERT(Aig_Regular(pObj) == pObj);
    int iObj = Aig_ObjId(pObj);

    Cnf_Dat_t *pCnf = &*frame.cnf();

    // pObj has no CNF variables -- recurs on children
    if (Aig_ObjIsAnd(pObj) && pCnf->pObj2Count[iObj] == -1) {
      addTrLogicForObj(unroller, frame, Aig_ObjFanin0(pObj));
      addTrLogicForObj(unroller, frame, Aig_ObjFanin1(pObj));
      return;
    }

    // -- already in sat solver
    if (frame.isCommittedObj(pObj))
      return;

    if (Aig_ObjIsAnd(pObj) || Aig_ObjIsCo(pObj)) {
      AVY_ASSERT(!Aig_ObjIsConst1(pObj));
      // -- recursively add children
      addTrLogicForObj(unroller, frame, Aig_ObjFanin0(pObj));
      if (Aig_ObjIsAnd(pObj))
        addTrLogicForObj(unroller, frame, Aig_ObjFanin1(pObj));

      // -- add clauses for pObj

      // -- save that pObj is committed
      frame.commitObj(pObj);

      int nClas = pCnf->pObj2Count[iObj];
      int iCla = pCnf->pObj2Clause[iObj];
      for (int i = 0; i < nClas; i++) {
        int *pClauseThis = pCnf->pClauses[iCla + i];
        int *pClauseNext = pCnf->pClauses[iCla + i + 1];
        if (!unroller.addClause(pClauseThis, pClauseNext, frame.frameNum())) {
          vout() << "SAT solver became UNSAT after adding clauses.\n";
          break;
        }
      }
    } else if (Aig_ObjIsConst1(pObj)) {
      // constant 1 node
      lit l = toLit(pCnf->pVarNums[iObj]);
      unroller.addClause(&l, &l + 1, frame.frameNum());
    } else
      AVY_ASSERT(Aig_ObjIsCi(pObj));
  }

public:
    /**
     * returns the input registers for the initial frame
     * exposed because they have to have an id in the global
     * lemma database
     */
    Clauses getInit()
    {
      FrameInfo * pFrame = frame(0);
      AVY_ASSERT(pFrame->hasCnf());
      AVY_ASSERT(pFrame->hasTr());
      Clauses clauses;
      //Aig_Obj_t *pObj;
      //int i;
      //Saig_ManForEachLo(&*pFrame->tr(), pObj, i){
        /// YV: This is supposed to work instead of the above.
      for (int i = 0; i < Saig_ManRegNum(&*pFrame->tr()); i++) {
        // -- cls is a unit clause
        // -- It asserts that the i th input is false
        Clause cls;
        cls.push_back(toLitCond(i, 1));
        clauses.push_back(cls);
        //reset cls
        cls.pop_back();
        }
      return clauses;
    }
  /**
     Recursively add all Tr logic necessary to drive regs outputs at
     the current frame of the unroller.
     Does not assume that sat-solver can deal with duplicate clauses
  */
  template <typename S>
  void addTrLogicRec(Unroller<S> &unroller, const IntVector &regs,int start=-1) {
    IntVector support0, support1;
    support1 = regs;
    start=start==-1?unroller.frame():start;
    for (int i = start; !support1.empty() && i >= 0; --i) {
      FrameInfo *pFrame = frame(i);
      addTrLogic(unroller, *pFrame, support1);
      if (i > 0) {
        support0 = support1;
        support1.clear();
        Aig_GetSupport(&*pFrame->tr(), support0, support1);
      }
    }
  }
  /**
     Resets all frames
   */
  void reset() {
    m_frames.clear();
  }

  /**
     Recursively add all pre- and post- conditions
     Assumes that sat-solver can deal with duplicate clauses
  */
  template <typename S> void addCondLogicRec(Unroller<S> &unroller,int start=-1) {
    unsigned nFrame = start==-1?unroller.frame():start;

    for (int i = nFrame; i >= 0; --i) {
      FrameInfo *pFrame = frame(i);
      if(i==0 && !m_propagate)
      {
        addClauses(unroller, pFrame->getPreCond(), unroller.getInputs(0),
                   pFrame->frameNum(),m_lemmaAbs);
      }
      if (i > 0)
        addClauses(unroller, pFrame->getPreCond(), unroller.getInputs(i),
                   pFrame->frameNum(),m_lemmaAbs);
      addClauses(unroller, pFrame->getPostCond(), unroller.getOutputs(i),
                 pFrame->frameNum());
    }
  }

protected:
  /// Add logic for the pre- and post-conditions at the given frame
  template <typename S> void addCondLogic(Unroller<S> &unroller) {
    unsigned nFrame = unroller.frame();
    FrameInfo *pFrame = frame(nFrame);
    if(nFrame==0 && !m_propagate)
    {
      addClauses(unroller, pFrame->getPreCond(), unroller.getInputs(0),
                 pFrame->frameNum(),m_lemmaAbs);
    }
    else {
      // add pre-condition clauses
      addClauses(unroller, pFrame->getPreCond(), unroller.getInputs(nFrame),
                 pFrame->frameNum(),m_lemmaAbs);
    }
    addClauses(unroller, pFrame->getPostCond(), unroller.getOutputs(nFrame),
               pFrame->frameNum());
  }

public:
  template <typename S>
  void addBad(Unroller<S> &unroller, AigManPtr pBad = nullptr) {
    CnfPtr pCnfBad = m_cnfBad;
    if (pBad == nullptr)
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
      if (i < Saig_ManPiNum(&*m_Tr))
        unroller.addPrimaryInput(pCnfBad->pVarNums[pObj->Id]);
      else
        unroller.addInput(pCnfBad->pVarNums[pObj->Id]);
    }

    // -- glue
    unroller.glueOutIn();

    // -- add constraints for bad
    unroller.addCnf(&*pCnfBad);

    // -- assert bad output
    lit Lit = toLit(pCnfBad->pVarNums[Aig_ManCo(&*pBad, 0)->Id]);
    unroller.setBadLit(Lit);

    /** pre-condition clauses */
    if (nFrame < m_frames.size())
      /**
       * HG: The preconditions are encoded with assumption literal of bad
       * This frame is not safe and thus bad is not going to
       * be k-indutive with respect to this frame
       */
        addClauses(unroller, frame(nFrame)->getPreCond(),
                 unroller.getInputs(nFrame), nFrame,m_lemmaAbs);
  }

  std::vector<IntVector> getFrameEquivs() {
    std::vector<IntVector> equivs;
    for (const std::unique_ptr<FrameInfo> &f : m_frames) {
      equivs.push_back(f->getOutputEquivs());
    }
    return equivs;
  }
};
} // namespace avy
