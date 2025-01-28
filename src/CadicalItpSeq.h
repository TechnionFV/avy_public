#ifndef CADICAL_ITP_SEQ_H_
#define CADICAL_ITP_SEQ_H_

#include "aig/gia/gia.h"
#include "drup2itp.hpp"

namespace avy {

using std::set;
using std::unordered_map;
using std::vector;

struct CadicalItpSeq : public DRUP2ITP::ResolutionProofIterator {
  typedef typename CaDiCaL::Solver Solver;
  typedef typename DRUP2ITP::Clause Clause;
  typedef typename DRUP2ITP::Range Range;

  Gia_Man_t *m_pMan;
  int m_NumOfVars;
  const vector<int> &m_VarToModelVarId;
  unsigned int seqSize;
  vector<vector<unsigned>> itpForVar;
  // Basel: Drop uint_64 hash tables and allocate vectors of size maximal clause
  // ID.
  vector<unordered_map<uint64_t, int>> clauseToItp;
  vector<int> numOfShared;
  vector<vector<int>> sharedLeaves;
  vector<set<uint64_t>> knownShared;
  vector<set<unsigned>> knownSharedUnits;
  const vector<int> &m_Assumptions;
  const DRUP2ITP::MiniTracer &m_tracer;

public:
  CadicalItpSeq(int solver_nVars, int numOfVars, const vector<int> &vars2vars,
                unsigned size, const vector<int> &assumes,
                const DRUP2ITP::MiniTracer &tracer)
      : m_NumOfVars(numOfVars), m_VarToModelVarId(vars2vars), seqSize(size),
        itpForVar(size), clauseToItp(size), m_Assumptions(assumes),
        m_tracer(tracer) {
    m_pMan = Gia_ManStart(numOfVars);
    m_pMan->pName = Abc_UtilStrsav(const_cast<char *>("itp"));
    Gia_ManHashStart(m_pMan);
    for (unsigned i = 0; i < numOfVars; i++) Gia_ManAppendCi(m_pMan);

    for (int i = 0; i < seqSize; i++) itpForVar[i].resize(solver_nVars, -1);

    numOfShared.resize(size, 0);
    sharedLeaves.resize(size);
    knownShared.resize(size);
  }

  virtual ~CadicalItpSeq() {
    Gia_ManHashStop(m_pMan);
    Gia_ManStop(m_pMan);
  }

  Gia_Man_t *getInterpolantMan() {
    printShared();
    return m_pMan;
  }
  const vector<vector<int>> &getSharedLeaves() { return sharedLeaves; }

  virtual void resolution(int resolvent, int p1, Clause *p2) {
    // dump_resolvent(resolvent);
    // dump_antecedents(p1, p2);
    int label1, label2, label;
    unsigned idx;
    for (int part = 1; part <= seqSize; part++) {
      label1 = getLabel(part, p1);
      label2 = getLabel(part, p2);
      label = getLabelByPivot(p1, part, label1, label2);
      idx = IDX(resolvent);
      assert(idx < itpForVar[part - 1].size());
      itpForVar[part - 1][idx] = label;
    }
  }

  virtual void chain_resolution(int parent) {
    // dump_resolvent(parent);
    // dump_antecedents();
    assert(chain.pivots.size());
    const unsigned idx = IDX(parent);
    for (int part = 1; part <= seqSize; part++) {
      int label = getLabel(part, this->chain.clauses[0]);
      auto &itpVec = itpForVar[part - 1];
      for (int pivot : chain.pivots)
        label = getLabelByPivot(pivot, part, label, getLabel(part, pivot));
      itpVec[idx] = label;
    }
  }

  virtual void chain_resolution(Clause *parent) {
    assert(this->chain.pivots.size() > 0);
    assert(this->chain.clauses.size() > 0);
    assert(this->chain.pivots.size() == this->chain.clauses.size() - 1);
    // dump_resolvent(parent);
    // dump_antecedents();
    const Clause *c = this->chain.clauses[0];
    for (int part = 1; part <= seqSize; part++) {
      if (parent && parent->range.max() <= part) {
        bool bTreatShared = false, bShared = true;
        for (int lit : *parent) {
          const Range &r = m_tracer.range(lit);
          if (r.min() != part || r.max() <= part) bShared = false;
        }
        if (bShared) {
          bTreatShared = true;
          for (Clause *c : chain.clauses) {
            if (!c) { // For now, not sure how to handle this
              bTreatShared = false;
              break;
            }
            // If the minimum partition is the current one then
            // this clause is OK, no need to check
            if (c->range.min() >= part) continue;
            // If the max partition equals or greater than the current
            // one, and the minimum is less than the current partition
            // this clause is bad.
            if (c->range.max() >= part) bTreatShared = false;
            // Otherwise, this clause needs to be a known good shared clause.
            // If not, a bad clause
            assert(c->range.max() <= knownShared.size());
            const auto &known = knownShared[c->range.max() - 1];
            if (known.find(c->id) == known.end()) bTreatShared = false;
            if (!bTreatShared) break;
          }
          if (bTreatShared) knownShared[part - 1].insert(parent->id);
        }

        visitLeaf(parent, part, bTreatShared);
        continue;
      }

      auto &clsToItp = clauseToItp[part - 1];
      int label = getLabel(part, c);

      int sz = this->chain.clauses.size() - 1;
      for (int i = 0; i < sz; i++) {
        unsigned pivot = IDX(this->chain.pivots[i]);
        Clause *c = this->chain.clauses[i + 1];
        if (c) {
          label = getLabelByPivot(this->chain.pivots[i], part, label, getLabel(part, c));
          continue;
        }
        assert(itpForVar[part - 1].size() > pivot);
        int l = getLabel(part, this->chain.pivots[i]);
        assert (l != -1 || !m_tracer.reason((this->chain.pivots[i])));
        if (l != -1)
          label = getLabelByPivot(pivot, part, label, l);
      }

      if (parent) {
        clsToItp[parent->id] = label;
        if (parent->size == 1)
          itpForVar[part - 1][IDX(parent->literals[0])] = label;
      } else {
        for (int leaf : sharedLeaves[part - 1])
          label = Gia_ManHashAnd(m_pMan, label, leaf);
        Gia_ManAppendCo(m_pMan, label);
      }
    }
  }

private:
  bool isAssumption(int lit) const {
    for (int ass : m_Assumptions)
      if (abs(ass) == abs(lit)) return true;
    return false;
  }

  void visitLeaf(const Clause *c, int part, bool bTreatShared) {
    assert(c);
    int label = Gia_ManConst1Lit();
    if (c->range.max() <= part) label = markLeaf(part, c, bTreatShared);
    clauseToItp[part - 1][c->id] = label;
    unsigned idx = IDX(c->literals[0]);
    if (c->size == 1 && itpForVar[part - 1][idx] == -1)
      itpForVar[part - 1][idx] = label;
  }

  int markLeaf(int part, const Clause *c, bool bTreatShared) {
    assert(c);
    Gia_Obj_t *pLabel = Gia_ManConst0(m_pMan);
    int label = Gia_ObjToLit(m_pMan, pLabel);
    bool bAllAreShared = true;
    for (int lit : *c) {
      const Range &r = m_tracer.range(lit);
      if (r.min() != part || r.max() <= part || isAssumption(lit)) {
        bAllAreShared = false;
        continue;
      }
      assert(r.max() - r.min() <= 1);
      assert(m_VarToModelVarId.size() > IDX(lit));
      int varId = m_VarToModelVarId[IDX(lit)];
      assert(varId >= 0 && varId < m_NumOfVars);
      Gia_Obj_t *pLeaf = Gia_ManCi(m_pMan, varId);
      if (lit < 0) pLeaf = Gia_Not(pLeaf);
      label = Gia_ManHashOr(m_pMan, label, Gia_ObjToLit(m_pMan, pLeaf));
      pLabel = Gia_Lit2Obj(m_pMan, label);
    }
    if (bAllAreShared && bTreatShared == true) {
      sharedLeaves[part - 1].push_back(label);
      numOfShared[part - 1] = numOfShared[part - 1] + 1;
      label = Gia_ManConst1Lit();
    }
    return label;
  }

  int getLabel(int part, int lit) {
    assert(part > 0 && part <= seqSize && lit);
    unsigned idx = IDX(lit);
    assert(itpForVar[part - 1].size() > idx);
    int label = itpForVar[part - 1][idx];
    if (label == -1) {
      const Clause *reason = m_tracer.reason(lit);
      assert(reason || isAssumption(lit));
      if (reason) {
        assert(reason && reason->original);
        assert(reason->size == 1 && reason->literals[0] == lit);
        visitLeaf(reason, part, false);
        label = itpForVar[part - 1][idx];
        assert (label != -1);
      }
    }
    return label;
  }

  int getLabel(int part, const Clause *c) {
    assert(part > 0 && part <= seqSize);
    unsigned id = c->id;
    auto &clsToItp = clauseToItp[part - 1];
    auto it = clsToItp.find(id);
    if (it == clsToItp.end()) {
      visitLeaf(c, part, false);
      return clsToItp[id];
    }
    return it->second;
  }

  int getLabelByPivot(int lit, int part, int label1, int label2) {
    if (label1 == label2) return label1;
    Range r = m_tracer.range(lit);
    if (r.min() <= part && r.max() <= part)
      return Gia_ManHashOr(m_pMan, label1, label2);
    return Gia_ManHashAnd(m_pMan, label1, label2);
  }

  void printShared() {
    LOG("shared", for (int i = 0; i < seqSize; i++) outs()
                      << "Element " << i << ": " << numOfShared[i] << "\n";);
  }

  // For debugging purposes only
  void dump_range(const Range &r) const {
    LOG("cadical_proof", logs() << "RANGE " << r.min() << "-" << r.max(););
  }

  void dump_resolvent(int parent) const {
    LOG("cadical_proof", logs() << "RESOLVENT;  " << parent << " ";);
    dump_range(m_tracer.range(parent));
    LOG("cadical_proof", logs() << "\n";);
  }

  void dump_resolvent(Clause *c) const {
    LOG("cadical_proof", logs() << "RESOLVENT;  ";);
    if (c) LOG("cadical_proof", for (int lit : *c) logs() << lit << " ";);
    LOG("cadical_proof", logs() << "0 ";);
    if (c) dump_range(c->range);
    LOG("cadical_proof", logs() << "\n";);
  }

  void dump_antecedents() const {
    LOG("cadical_proof", logs() << "ANTECEDENTS;\n";);
    for (const auto &c : chain.clauses) {
      LOG("cadical_proof", logs() << " * ";);
      if (c) LOG("cadical_proof", for (int lit : *c) logs() << lit << " ";);
      LOG("cadical_proof", logs() << "0 ";);
      if (c) dump_range(c->range);
      LOG("cadical_proof", logs() << "\n";);
    }
  }

  void dump_antecedents(int p1, Clause *p2) const {
    LOG("cadical_proof", logs() << "ANTECEDENTS;\n";);
    LOG("cadical_proof", logs() << " * " << p1 << " 0 ";);
    dump_range(m_tracer.range(p1));
    LOG("cadical_proof", logs() << "\n * ";);
    assert(p2);
    LOG("cadical_proof", for (int lit : *p2) logs() << lit << " ";);
    LOG("cadical_proof", logs() << "0 ";);
    dump_range(p2->range);
    LOG("cadical_proof", logs() << "\n";);
  }

  unsigned IDX(int lit) const {
    assert(lit);
    return abs(lit) - 1;
  }
};
} // namespace avy

#endif /* CADICAL_ITP_SEQ_H_ */
