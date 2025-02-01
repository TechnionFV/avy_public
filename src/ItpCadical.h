#ifndef _ITP_Cadical_H_
#define _ITP_Cadical_H_

#include "AigUtils.h"
#include "AvyTypes.h" //IntVector
#include "avy/Util/AvyDebug.h"
#include "avy/Util/AvyTribool.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"
#include "boost/noncopyable.hpp"
#include "drup2itp.hpp"
#include <vector>

#include <chrono>
#include <iostream>

class MinimizerReplay : public DRUP2ITP::ItpClauseIterator {
  CaDiCaL::Solver m_solver;
  DRUP2ITP::Drup2Itp m_tracer;

public:
  MinimizerReplay(int vars, bool preprocessing, bool inprocessing) : m_solver() {
    bool configured = m_solver.configure("unsat");
    if (!preprocessing)
      configured &= m_solver.configure("plain");
    assert (configured);
    m_solver.set("inprocessing", inprocessing);
    m_tracer.connect_to(m_solver);
    m_tracer.set_current_partition(1);
    m_tracer.resize(vars);
    m_solver.reserve(vars);
  }

  ~MinimizerReplay() { m_solver.disconnect_proof_tracer(&m_tracer); }

  DRUP2ITP::MiniTracer mini_tracer() const { return m_tracer.mini_tracer(); }

  bool clause(const DRUP2ITP::Clause *c) {
    assert(c && c->range.singleton ());
    m_tracer.set_current_partition(c->range.min ());
    for (int lit : *c)
      m_solver.add (lit);
    m_solver.add (0);
    return true;
  }

  bool assume(int lit) {
    m_solver.assume(lit);
    return true;
  }

  bool replay(DRUP2ITP::ResolutionProofIterator &it) {
    m_solver.solve();
    assert(m_solver.status() == 20);
    bool trimmed = m_tracer.trim(nullptr, false);
    assert(trimmed);
    bool replayed = m_tracer.replay(it, false);
    assert(replayed);
    return true;
  }
};

namespace avy {
using namespace abc;

class ItpCadical : boost::noncopyable {
  std::unique_ptr<CaDiCaL::Solver> m_pSat;
  std::unique_ptr<DRUP2ITP::Drup2Itp> m_tracer;
  bool m_Trivial;
  bool m_Simplifier;
  unsigned m_nParts;
  avy::tribool m_State;
  IntVector m_core, m_Assumptions;

  tribool tobool(int s) {
    tribool r;
    switch (s) {
    case 10:
      r = true;
      break;
    case 20:
      r = false;
      break;
    default:
      AVY_ASSERT(s == 0);
    }
    return r;
  }

  int toCadicalLit(int lit) {
    int v = (lit >> 1) + 1;
    AVY_ASSERT(v > 0);
    return (lit & 1) ? -v : v;
  }

  int toAvyLit(int lit) {
    AVY_ASSERT(lit);
    return 2 * (abs(lit) - 1) + int(lit < 0);
  }

public:
  /// create a solver with nParts partitions and nVars variables
  ItpCadical(unsigned nParts, unsigned nVars, bool simp = true)
      : m_pSat(nullptr), m_tracer(nullptr), m_Simplifier(simp) {
    reset(nParts, nVars);
  }

  ~ItpCadical() { m_pSat->disconnect_proof_tracer(m_tracer.get()); }

  void reset(unsigned nParts, unsigned nVars) {
    AVY_ASSERT(nParts >= 2 && "require at least 2 partitions");
    m_nParts = nParts;
    m_Trivial = false;
    m_State = avy::tribool();
    DRUP2ITP::Drup2Itp *tracer = m_tracer.get();
    if (tracer) m_pSat->disconnect_proof_tracer(tracer);
    m_pSat.reset(new CaDiCaL::Solver());
    m_tracer.reset(new DRUP2ITP::Drup2Itp);
    m_tracer->connect_to(*m_pSat.get());
    m_tracer->set_current_partition(1);
    m_tracer->set_reorder_proof(gParams.proof_reorder);
    if (!m_Simplifier) m_pSat->configure("plain");
    m_pSat->set("inprocessing", gParams.cadical_itp_inprocessing);
  }

  void markPartition(unsigned nPart) {
    AVY_ASSERT(nPart > 0);
    if (nPart > m_nParts) m_nParts = nPart;
    m_tracer->set_current_partition(nPart);
  }

  void reserve(int nVars) { m_pSat->reserve(nVars); }

  bool addUnit(int unit) {
    m_pSat->clause(toCadicalLit(unit));
    m_Trivial = m_pSat->inconsistent();
    return !m_Trivial;
  }

  bool addClause(int *bgn, int *end) {
    std::vector<int> cls;
    for (int *it = bgn; it != end; ++it) cls.push_back(toCadicalLit(*it));
    m_pSat->clause(cls);
    m_Trivial = m_pSat->inconsistent();
    return !m_Trivial;
  }

  bool addClause(int *bgn, int *end, int nameLit) {
    AVY_ASSERT(nameLit >= 0);
    std::vector<int> cls;
    for (int *it = bgn; it != end; ++it) cls.push_back(toCadicalLit(*it));
    cls.push_back(-toCadicalLit(nameLit));
    m_pSat->clause(cls);
    m_Trivial = m_pSat->inconsistent();
    return !m_Trivial;
  }

  void dumpCnf(std::string fname) {
    m_pSat->write_dimacs(const_cast<char *>(fname.c_str()), m_pSat->vars());
  }

  CaDiCaL::Solver *get() { return m_pSat.get(); }

  /// true if the context is decided
  bool isSolved() { return m_Trivial || m_State || !m_State; }

  int core(int **out) {
    m_core.clear();
    for (int lit : m_Assumptions)
      if (m_pSat->failed(lit)) m_core.push_back(toAvyLit(-lit));
    *out = &m_core[0];
    return m_core.size();
  }

  avy::tribool solve(const IntVector &assumptions, int minElem = 0,
                     int maxSize = -1) {
    AVY_ASSERT(minElem >= 0 && minElem < assumptions.size());
    ScoppedStats __stats__("ItpCadical_solve");

    if (m_Trivial || m_pSat->inconsistent()) return false;

    int max = assumptions.size();
    if (maxSize >= 0 && maxSize < max) max = maxSize;

    m_Assumptions.clear();
    m_pSat->reset_assumptions();

    int lit;
    for (unsigned i = 0; i < max; ++i) {
      lit = toCadicalLit(assumptions[i]);
      m_pSat->assume(lit), m_Assumptions.push_back(lit);
    }

    return tobool(m_pSat->solve());
  }

  avy::tribool solve() {
    ScoppedStats __stats__("ItpCadical_solve");
    return tobool(m_pSat->solve());
  }

  bool isTrivial() { return m_Trivial; }

  void setFrozen(int v, bool p) {
    int l = toLit(v);
    if (p)
      m_pSat->freeze(abs(toCadicalLit(l)));
    else
      m_pSat->melt(abs(toCadicalLit(l)));
  }

  void markSelector(int v, bool p) { setFrozen(v, p); }

  Aig_Man_t *getInterpolant(lit, std::vector<Vec_Int_t *> &, int, bool = true);

  tribool getVarVal(int v) {
    int l = toLit(v);
    AVY_ASSERT(m_pSat->state() & CaDiCaL::SATISFIED);
    return m_pSat->val(abs(toCadicalLit(l))) > 0;
  }

  unsigned getNumOfConflicts() const { return m_pSat->conflicts(); }

  void setBudget(int nBudget) {
    bool configured = m_pSat->limit("conflicts", nBudget);
    assert(configured);
  }
};

} // namespace avy

#endif /* _ITP_Cadical_H_ */
