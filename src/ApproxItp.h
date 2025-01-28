#ifndef _APPROX_ITP_H_
#define _APPROX_ITP_H_

#include "ItpSequence.h"
#include "aig/gia/gia.h"
#include "sat/bsat/satClause.h"
#include "AvyTypes.h" //IntVector and Clause
#include <unordered_set>
#include <vector>

namespace avy {
// template <typename T>
// class ProofLoggingTrait   {  };

template <typename T>
class ApproxItp : public ProofLoggingTrait<T>::ProofVisitor {
  typedef ProofLoggingTrait<T> PfTrait;
  typedef typename PfTrait::ProofVisitor ProofVisitor;
  typedef typename PfTrait::Solver Solver;
  typedef typename PfTrait::Var Var;
  typedef typename PfTrait::Lit Lit;
  typedef typename PfTrait::CRef CRef;
  typedef typename PfTrait::Clause Clause;
  typedef typename PfTrait::IntVec IntVec;
  typedef typename PfTrait::IntIntVec IntIntVec;
  typedef typename PfTrait::VecIntIntVec VecIntIntVec;
  typedef typename PfTrait::IntCMap IntCMap;
  typedef typename PfTrait::CMapIntVec CMapIntVec;
  typedef typename PfTrait::VecIntCMap VecIntCMap;
  typedef typename PfTrait::VecCMapIntVec VecCMapIntVec;
  typedef typename PfTrait::Range Range;


  const Solver &m_Solver; // -- The SAT instance
  Sat_Mem_t m_ClauseMan;
  IntIntVec m_ApproxSeq;
  int m_NumOfVars;
  const IntVector &m_VarToModelVarId;

  unsigned int seqSize;      // -- ItpSeq size, always greater than 0.
  VecIntIntVec itpForVar;    // -- Itp labeling on the trail
  VecCMapIntVec clauseToItp; // -- Clause to its Itp labeling

  std::vector<std::vector<std::unordered_set<int>>> occurs;

public:
  ApproxItp(Solver &s, int numOfVars, const IntVector &vars2vars,
            unsigned size)
      : ProofVisitor(), m_Solver(s), m_ApproxSeq(size), m_NumOfVars(numOfVars),
        m_VarToModelVarId(vars2vars), seqSize(size), clauseToItp(size),
        itpForVar(size), occurs(size) {
    Sat_MemAlloc_(&m_ClauseMan, 14);

    for (int i = 0; i < seqSize; i++) {
      itpForVar[i].growTo(s.nVars(), IntVec());
      occurs[i].resize(s.nVars());
    }
  }

  virtual ~ApproxItp() { Sat_MemFree_(&m_ClauseMan); }

  // Gia_Man_t*                             getInterpolantMan() { return m_pMan;
  // }

  void visitLeaf(CRef cls, const Clause &c, int part) {
    Var v = var(c[0]);
    const Range &r = c.part();
    // assert(r.min() == r.max());
    int h = -1;
    if (r.max() <= part)
      h = markLeaf(part, cls, c);
    IntVec clsVec;
    clsVec.push(h);
    clauseToItp[part - 1].insert(cls, clsVec);
    if (c.size() == 1 && itpForVar[part - 1][v].size() == 0)
      itpForVar[part - 1][v].push(h);
  }

  virtual int visitResolvent(Lit resolvent, Lit p1, CRef p2) {
    Var v = PfTrait::var(resolvent);
    Var v1 = PfTrait::var(p1);
    for (int part = 1; part <= seqSize; part++) {
      IntIntVec &itpVec = itpForVar[part - 1];
      assert(itpVec.size() > v1);
      if (itpVec[v1].size() == 0) {
        CRef r = m_Solver.getReason(v1);
        const Clause &c1 = m_Solver.getClause(r);
        assert(c1.learnt() == false);
        assert(c1.size() == 1);
        visitLeaf(r, c1, part);
      }
      assert(itpVec[v1].size() > 0);
      IntVec clauses2;
      bool res = clauseToItp[part - 1].has(p2, clauses2);
      if (res == false) {
        const Clause &c2 = m_Solver.getClause(p2);
        assert(c2.learnt() == false);
        visitLeaf(p2, c2, part);
      }

      IntVec clauses;
      getLabelByPivot(v1, part, itpVec[v1], clauseToItp[part - 1][p2], clauses);
      clauses.copyTo(itpVec[v]);
    }
    return 0;
  }

  virtual int visitChainResolvent(Lit parent) {
    Var v = PfTrait::var(parent);
    CRef c = this->chainClauses[0];
    int size = this->chainPivots.size();
    assert(size > 0);
    for (int part = 1; part <= seqSize; part++) {
      IntVec clauses;
      bool res = clauseToItp[part - 1].has(c, clauses);
      if (res == false) {
        visitLeaf(c, m_Solver.getClause(c), part);
        res = clauseToItp[part - 1].has(c, clauses);
        assert(res == true);
      }

      IntIntVec &itpVec = itpForVar[part - 1];
      for (int i = 0; i < size; i++) {
        Var pivot = PfTrait::var(this->chainPivots[i]);
        if (itpVec[pivot].size() == 0) {
          CRef r = m_Solver.getReason(pivot);
          const Clause &pC = m_Solver.getClause(r);
          assert(pC.part().min() == pC.part().max());
          assert(pC.size() == 1);
          visitLeaf(r, pC, part);
        }
        assert(itpVec[pivot].size() == 0);

        IntVec resClauses;
        getLabelByPivot(pivot, part, clauses, itpVec[pivot], resClauses);
        resClauses.moveTo(clauses);
      }

      clauses.moveTo(itpVec[v]);
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
        /**
         * Do not handle Shared leaves for now
         *
        bool bTreatShared = false;
        const Clause& cP = m_Solver.getClause(parent);
        bool bShared = true;
        for (int i=0; i < cP.size(); i++)
        {
            Var x = PfTrait::var(cP[i]);
            Range r = m_Solver.getVarRange(x);
            if (r.min() != part || r.max() <= part)
                bShared = false;
        }
        if (bShared)
        {
            bTreatShared = true;
            for (int jj=0; jj < this->chainClauses.size() && bTreatShared; jj++)
        { CRef xx  = this->chainClauses[jj]; if (xx == PfTrait::CRef_Undef ) {
        // For now, not sure how to handle this bTreatShared = false; break;
                }
                const Clause& c = m_Solver.getClause(xx);
                // If the minimum partition is the current one then
                // this clause is OK, no need to check
                if (c.part().min() >= part) continue;

                // If the max partition equals or greater than the current
                // one, and the minimum is less than the current partition
                // this clause is bad.
                if (c.part().max() >= part) bTreatShared = false;

                // Otherwise, this clause needs to be a known good shared
        clause.
                // If not, a bad clause
                if (knownShared[c.part().max()-1].find(xx) ==
        knownShared[c.part().max()-1].end()) bTreatShared = false;
            }

            if (bTreatShared) {
                knownShared[part-1].insert(parent);
            }
          }
          */
        visitLeaf(parent, m_Solver.getClause(parent), part);
        continue;
      }

      IntCMap &clsToItp = clauseToItp[part - 1];
      IntIntVec &itpVec = itpForVar[part - 1];
      IntVec label;
      bool res = clsToItp.has(c, label);
      if (res == false) {
        const Clause &cls = m_Solver.getClause(c);
        assert(cls.part().min() == cls.part().max());
        visitLeaf(c, cls, part, false);
        clauseToItp[part - 1][c].copyTo(label);
      }

      int i = 0;
      int size = this->chainClauses.size();
      for (; i < size - 1; i++) {
        Var pivot = PfTrait::var(this->chainPivots[i]);
        IntVec l;
        CRef r = this->chainClauses[i + 1];
        if (r != PfTrait::CRef_Undef) {
          res = clsToItp.has(r, l);
          if (res == false) {
            const Clause &cls = m_Solver.getClause(r);
            assert(cls.part().min() == cls.part().max());
            visitLeaf(r, cls, part);
            clauseToItp[part - 1][r].copyTo(l);
          }
          IntVec resClause;
          label = getLabelByPivot(pivot, part, label, l, resClause);
          resClause.moveTo(label);
        } else {
          assert(itpVec.size() > pivot);
          IntVec &l = itpVec[pivot];
          if (itpVec[pivot].size() == 0) {
            CRef r = m_Solver.getReason(pivot);
            const Clause &cls = m_Solver.getClause(r);
            assert(cls.part().min() == cls.part().max());
            assert(cls.size() == 1);
            visitLeaf(r, cls, part);
          }
          assert(itpVec[pivot].size() != 0);
          IntVec resClause;
          getLabelByPivot(pivot, part, label, l, resClause);
          resClause.moveTo(label);
        }
      }

      if (parent != PfTrait::CRef_Undef) {
        clsToItp.insert(parent, label);
        const Clause &cP = m_Solver.getClause(parent);
        if (cP.size() == 1)
          label.copyTo(itpForVar[part - 1][var(cP[0])]);
      } else {
        // Eliminate all locals first
        label.copyTo(m_ApproxSeq[part - 1]);
      }
    }
    return 0;
  }

private:
  int markLeaf(int part, CRef cr, const Clause &c) {
    lit clause[c.size()];
    for (int i = 0; i < c.size(); i++) {
      Var x = PfTrait::var(c[i]);
      lit l = toLitCond(x, PfTrait::sign(c[i]));

      clause[i] = l;
    }

    int h = Sat_MemAppend(&m_ClauseMan, clause, c.size(), 0, 0);
    for (int i = 0; i < c.size(); i++) {
      lit l = clause[i];
      int var = lit_var(l);
      occurs[part - 1][var].insert(h);
    }
    return h;
  }

  void getLabelByPivot(Var pivot, int part, const IntVec &clauses1,
                       const IntVec &clauses2, IntVec &clauses) {
    Range r = m_Solver.getVarRange(pivot);
    if (r.min() <= part &&
        r.max() <=
            part) { // -- Interpolation for (A,B) pair - partition 1 = localA
      eliminate(pivot, part, clauses1, clauses2, clauses);
    } else {
      clauses1.copyTo(clauses);
      for (int i = 0; i < clauses2.size(); i++)
        clauses.push(clauses2[i]);
    }
  }

  void eliminate(Var v, int part, const IntVec &clauses1,
                 const IntVec &clauses2, IntVec &clauses) {
    std::unordered_set<int> &occ = occurs[part - 1][v];
    std::unordered_set<int>::const_iterator it;
    IntVector pos, neg;

    IntVec inputClauses;
    clauses1.copyTo(inputClauses);
    for (int cls = 0; cls < clauses2.size(); cls++)
      inputClauses.push(cls);

    // Iterate over all input clauses
    for (int cls = 0; cls < inputClauses.size(); cls++) {
      // Check if the clause is in the occurrence
      if (occ.find(cls) == occ.end()) {
        clauses.push(cls);
        continue;
      }

      clause *c = Sat_MemClauseHand(&m_ClauseMan, cls);
      lit *begin = clause_begin(c);
      int size = clause_size(c);

      // Iterate over all literals
      for (int i = 0; i < size; i++) {
        lit l = begin[i];
        if (lit_var(l) == v) {
          // Found the occurrence, push to either neg or pos
          (lit_sign(l) ? neg : pos).push_back(cls);
          break;
        }
      }
    }

    // Now decide
    Clause tmp;
    if (neg.size() * pos.size() <= neg.size() + pos.size()) {
      // Do elimination - cross product
      for (int i = 0; i < pos.size(); i++) {
        clause *p = Sat_MemClauseHand(&m_ClauseMan, pos[i]);
        for (int j = 0; j < neg.size(); j++) {
          clause *q = Sat_MemClauseHand(&m_ClauseMan, neg[j]);
          if (merge(p, q, v, tmp)) {
            lit clause[tmp.size()];
            for (int l = 0; l < tmp.size(); l++)
              clause[i] = tmp[l];
            int h = Sat_MemAppend(&m_ClauseMan, clause, tmp.size(), 0, 0);
            clauses.push(h);
          }
        }
      }
    } else {
      // Skip elimination
      for (int i = 0; i < neg.size(); i++)
        clauses.push(neg[i]);
      for (int i = 0; i < pos.size(); i++)
        clauses.push(pos[i]);
    }
  }

  bool merge(clause *_ps, clause *_qs, Var v, Clause &out_clause) {
    out_clause.clear();

    bool ps_smallest = clause_size(_ps) < clause_size(_qs);
    clause *ps = ps_smallest ? _qs : _ps;
    clause *qs = ps_smallest ? _ps : _qs;

    for (int i = 0; i < clause_size(qs); i++) {
      if (lit_var(clause_begin(qs)[i]) != v) {
        for (int j = 0; j < clause_size(ps); j++)
          if (lit_var(clause_begin(ps)[j]) == lit_var(clause_begin(qs)[i])) {
            if (clause_begin(ps)[j] == lit_neg(clause_begin(qs)[i]))
              return false;
            else
              goto next;
          }
        out_clause.push_back(clause_begin(qs)[i]);
      }
    next:;
    }

    for (int i = 0; i < clause_size(ps); i++)
      if (lit_var(clause_begin(ps)[i]) != v)
        out_clause.push_back(clause_begin(ps)[i]);

    return true;
  }
};

} // namespace avy

#endif //_APPROX_ITP_H_
