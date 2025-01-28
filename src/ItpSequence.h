#ifndef _ITP_SEQUENCE_H_
#define _ITP_SEQUENCE_H_

#include "aig/gia/gia.h"
#include "AvyTypes.h"
#include <set>
#include <vector>

namespace avy {
template <typename T> class ProofLoggingTrait {};

template <typename T>
class ItpSequence : public ProofLoggingTrait<T>::ProofVisitor {
  typedef ProofLoggingTrait<T> PfTrait;
  typedef typename PfTrait::ProofVisitor ProofVisitor;
  typedef typename PfTrait::Solver Solver;
  typedef typename PfTrait::Var Var;
  typedef typename PfTrait::Lit Lit;
  typedef typename PfTrait::CRef CRef;
  typedef typename PfTrait::Clause Clause;
  typedef typename PfTrait::IntVec IntVec;
  typedef typename PfTrait::IntIntVec IntIntVec;
  typedef typename PfTrait::IntCMap IntCMap;
  typedef typename PfTrait::VecIntCMap VecIntCMap;
  typedef typename PfTrait::Range Range;


  const Solver &m_Solver; // -- The SAT instance
  Gia_Man_t *m_pMan;      // -- Manager for the interpolant
  int m_NumOfVars;
  const IntVector &m_VarToModelVarId;

  unsigned int seqSize;   // -- ItpSeq size, always greater than 0.
  IntIntVec itpForVar;    // -- Itp labeling on the trail
  VecIntCMap clauseToItp; // -- Clause to its Itp labeling

  IntVector numOfShared;

  std::vector<IntVector> sharedLeaves;
  std::vector<std::set<CRef>> knownShared;
  std::vector<std::set<Var>> knownSharedUnits;

public:
  ItpSequence(Solver &s, int numOfVars, const IntVector &vars2vars,
              unsigned size)
      : ProofVisitor(), m_Solver(s), m_NumOfVars(numOfVars),
        m_VarToModelVarId(vars2vars), seqSize(size), itpForVar(size),
        clauseToItp(size) {
    m_pMan = Gia_ManStart(numOfVars);
    m_pMan->pName = Abc_UtilStrsav(const_cast<char *>("itp"));
    Gia_ManHashStart(m_pMan);
    for (unsigned i = 0; i < numOfVars; i++)
      Gia_ManAppendCi(m_pMan);

    for (int i = 0; i < seqSize; i++)
      itpForVar[i].growTo(s.nVars(), -1);

    numOfShared.resize(size, 0);
    sharedLeaves.resize(size);
    knownShared.resize(size);
  }

  virtual ~ItpSequence() {
    Gia_ManHashStop(m_pMan);
    Gia_ManStop(m_pMan);
  }

  Gia_Man_t *getInterpolantMan() {
    printShared();
    return m_pMan;
  }
  const std::vector<IntVector> &getSharedLeaves() {
    return sharedLeaves;
  }

  void visitLeaf(CRef cls, const Clause &c, int part, bool bTreatShared) {
    Var v = var(c[0]);
    int label = Gia_ManConst1Lit();
    const Range &r = c.part();
    // assert(r.min() == r.max());
    if (r.max() <= part)
      label = markLeaf(part, cls, c, bTreatShared);
    clauseToItp[part - 1].insert(cls, label);
    if (c.size() == 1 && itpForVar[part - 1][v] == -1)
      itpForVar[part - 1][v] = label;
  }

  virtual int visitResolvent(Lit resolvent, Lit p1, CRef p2) {
    Var v = PfTrait::var(resolvent);
    Var v1 = PfTrait::var(p1);
    for (int part = 1; part <= seqSize; part++) {
      IntVec &itpVec = itpForVar[part - 1];
      int label1, label2;
      assert(itpVec.size() > v1);
      label1 = itpVec[v1];
      if (label1 == -1) {
        CRef r = m_Solver.getReason(v1);
        const Clause &c1 = m_Solver.getClause(r);
        assert(c1.learnt() == false);
        assert(c1.size() == 1);
        visitLeaf(r, c1, part, false);
        label1 = itpVec[v1];
      }
      assert(label1 != -1);
      bool res = clauseToItp[part - 1].has(p2, label2);
      if (res == false) {
        const Clause &c2 = m_Solver.getClause(p2);
        assert(c2.learnt() == false);
        visitLeaf(p2, c2, part, false);
        label2 = clauseToItp[part - 1][p2];
      }

      int label = getLabelByPivot(v1, part, label1, label2);
      itpVec[v] = label;
    }
    return 0;
  }

  virtual int visitChainResolvent(Lit parent) {
    Var v = PfTrait::var(parent);
    CRef c = this->chainClauses[0];
    int size = this->chainPivots.size();
    assert(size > 0);
    for (int part = 1; part <= seqSize; part++) {
      int label;
      bool res = clauseToItp[part - 1].has(c, label);
      if (res == false) {
        visitLeaf(c, m_Solver.getClause(c), part, false);
        label = clauseToItp[part - 1][c];
      }
      IntVec &itpVec = itpForVar[part - 1];
      for (int i = 0; i < size; i++) {
        Var pivot = PfTrait::var(this->chainPivots[i]);
        int l = itpVec[pivot];
        if (l == -1) {
          CRef r = m_Solver.getReason(pivot);
          const Clause &pC = m_Solver.getClause(r);
          assert(pC.part().min() == pC.part().max());
          assert(pC.size() == 1);
          visitLeaf(r, pC, part, false);
          l = itpVec[pivot];
        }
        assert(l != -1);
        label = getLabelByPivot(pivot, part, label, l);
      }

      itpVec[v] = label;
    }
    return 0;
  }

  virtual int visitChainResolvent(CRef parent) {
    assert(this->chainPivots.size() > 0);
    assert(this->chainClauses.size() > 0);
    assert(this->chainPivots.size() == this->chainClauses.size() - 1);

    CRef c = this->chainClauses[0];
    for (int part = 1; part <= seqSize; part++) {
      if (parent != PfTrait::CRef_Undef &&
          m_Solver.getClause(parent).part().max() <= part) {
        bool bTreatShared = false;
        const Clause &cP = m_Solver.getClause(parent);
        bool bShared = true;
        for (int i = 0; i < cP.size(); i++) {
          Var x = PfTrait::var(cP[i]);
          Range r = m_Solver.getVarRange(x);
          if (r.min() != part || r.max() <= part)
            bShared = false;
        }
        if (bShared) {
          bTreatShared = true;
          for (int jj = 0; jj < this->chainClauses.size() && bTreatShared;
               jj++) {
            CRef xx = this->chainClauses[jj];
            if (xx ==
                PfTrait::CRef_Undef) { // For now, not sure how to handle this
              bTreatShared = false;
              break;
            }
            const Clause &c = m_Solver.getClause(xx);
            // If the minimum partition is the current one then
            // this clause is OK, no need to check
            if (c.part().min() >= part)
              continue;

            // If the max partition equals or greater than the current
            // one, and the minimum is less than the current partition
            // this clause is bad.
            if (c.part().max() >= part)
              bTreatShared = false;

            // Otherwise, this clause needs to be a known good shared clause.
            // If not, a bad clause
            if (knownShared[c.part().max() - 1].find(xx) ==
                knownShared[c.part().max() - 1].end())
              bTreatShared = false;
          }

          if (bTreatShared) {
            knownShared[part - 1].insert(parent);
          }
        }

        visitLeaf(parent, m_Solver.getClause(parent), part, bTreatShared);
        continue;
      }

      IntCMap &clsToItp = clauseToItp[part - 1];
      IntVec &itpVec = itpForVar[part - 1];
      int label;
      bool res = clsToItp.has(c, label);
      if (res == false) {
        const Clause &cls = m_Solver.getClause(c);
        assert(cls.part().min() == cls.part().max());
        visitLeaf(c, cls, part, false);
        label = clauseToItp[part - 1][c];
      }

      int i = 0;
      int size = this->chainClauses.size();
      for (; i < size - 1; i++) {
        Var pivot = PfTrait::var(this->chainPivots[i]);
        int l;
        CRef r = this->chainClauses[i + 1];
        if (r != PfTrait::CRef_Undef) {
          res = clsToItp.has(r, l);
          if (res == false) {
            const Clause &cls = m_Solver.getClause(r);
            assert(cls.part().min() == cls.part().max());
            visitLeaf(r, cls, part, false);
            l = clauseToItp[part - 1][r];
          }
          label = getLabelByPivot(pivot, part, label, l);
        } else {
          assert(itpVec.size() > pivot);
          int l = itpVec[pivot];
          if (l == -1) {
            CRef r = m_Solver.getReason(pivot);
            if (r != PfTrait::CRef_Undef) {
              const Clause &cls = m_Solver.getClause(r);
              assert(cls.part().min() == cls.part().max());
              assert(cls.size() == 1);
              visitLeaf(r, cls, part, false);
              l = itpVec[pivot];
            }
          }
          if (l != -1)
            label = getLabelByPivot(pivot, part, label, l);
          else
            assert(m_Solver.getReason(pivot) ==
                   PfTrait::CRef_Undef); // Can only happen with assumptions
        }
      }

      if (parent != PfTrait::CRef_Undef) {
        clsToItp.insert(parent, label);
        const Clause &cP = m_Solver.getClause(parent);
        if (cP.size() == 1)
          itpForVar[part - 1][var(cP[0])] = label;
      } else {
        const IntVector &leaves = sharedLeaves[part - 1];
        for (int j = 0; j < leaves.size(); j++) {
          int leaf = leaves[j];
          label = Gia_ManHashAnd(m_pMan, label, leaf);
        }
        Gia_ManAppendCo(m_pMan, label);
      }
    }
    return 0;
  }

private:
  int markLeaf(int part, CRef cr, const Clause &c, bool bTreatShared) {
    Gia_Obj_t *pLabel = Gia_ManConst0(m_pMan);
    int label = Gia_ObjToLit(m_pMan, pLabel);
    bool bAllAreShared = true;
    bool isAssumptionVar;
    for (int i = 0; i < c.size(); i++) {

      Var x = PfTrait::var(c[i]);
      isAssumptionVar = m_Solver.isSelector(x);
      Range r = m_Solver.getVarRange(x);
      if (r.min() == part && r.max() > part && !isAssumptionVar) {
        // outs () << "(min,max): (" << r.min() << "," << r.max() << ")\n";
        assert(r.max() - r.min() <= 1);
        // assert(r.min() <= r.max() + 1 && r.min() >= r.max() - 1);
        assert(m_VarToModelVarId.size() > x);
        int varId = m_VarToModelVarId[x];
        assert(varId >= 0 && varId < m_NumOfVars);

        Gia_Obj_t *pLeaf = Gia_ManCi(m_pMan, varId);
        if (PfTrait::sign(c[i]))
          pLeaf = Gia_Not(pLeaf);

        label = Gia_ManHashOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
        pLabel = Gia_Lit2Obj(m_pMan, label);
      } else
        bAllAreShared = false;
    }

    if (bAllAreShared && bTreatShared == true) {
      sharedLeaves[part - 1].push_back(label);
      numOfShared[part - 1] = numOfShared[part - 1] + 1;
      label = Gia_ManConst1Lit();
      // if (c.part().min() == c.part().max()) knownShared[part-1].insert(cr);
    }

    return label;
  }

  int getLabelByPivot(Var pivot, int part, int label1, int label2) {
    Range r = m_Solver.getVarRange(pivot);
    if (label1 == label2 && label1 == Gia_ManConst0Lit())
      return Gia_ManConst0Lit();
    if (label1 == label2 && label1 == Gia_ManConst1Lit())
      return Gia_ManConst1Lit();
    if (label1 == label2)
      return label1;
    if (r.min() <= part &&
        r.max() <=
            part) // -- Interpolation for (A,B) pair - partition 1 = localA
      return Gia_ManHashOr(m_pMan, label1, label2);

    return Gia_ManHashAnd(m_pMan, label1, label2);
  }

  void printShared() {
    LOG("shared", for (int i = 0; i < seqSize; i++) outs()
                      << "Element " << i << ": " << numOfShared[i] << "\n";);
  }
};

} // namespace avy

#endif
