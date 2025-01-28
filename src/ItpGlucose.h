#ifndef _ITP_GLUCOSE_H_
#define _ITP_GLUCOSE_H_

#include "boost/noncopyable.hpp"

#include "AigUtils.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"
#include "avy/Util/AvyTribool.h"
#include "AvyTypes.h" // IntVector

#include "glucose/simp/SimpSolver.h"

#include <vector>

namespace avy {
using namespace abc;

/// Thin wrapper around interpolating sat solver
class ItpGlucose : boost::noncopyable {
private:
  ::Glucose::SimpSolver *m_pSat;

  /// true if last result was trivial
  bool m_Trivial;
  bool m_Simplifier;

  /// number of partitions
  unsigned m_nParts;

  /// current state
  avy::tribool m_State;

  IntVector m_core;

  avy::tribool tobool(::Glucose::lbool v) {
    avy::tribool r;
    if (v == ::Glucose::lbool((uint8_t)0))
      r = true;
    else if (v == ::Glucose::lbool((uint8_t)1))
      r = false;
    return r;
  }

public:
  /// create a solver with nParts partitions and nVars variables
  ItpGlucose(unsigned nParts, unsigned nVars, bool simp = true)
      : m_pSat(0), m_Simplifier(simp) {
    reset(nParts, nVars);
  }

  ~ItpGlucose() {
    if (m_pSat)
      delete m_pSat;
    m_pSat = NULL;
  }

  /// reset and allocate nParts partitions and nVars variables
  void reset(unsigned nParts, unsigned nVars) {
    AVY_ASSERT(nParts >= 2 && "require at least 2 partitions");
    if (m_pSat)
      delete m_pSat;
    m_nParts = nParts;
    m_Trivial = false;
    m_State = avy::tribool();
    m_pSat = new ::Glucose::SimpSolver();
    m_pSat->reorderProof(gParams.proof_reorder);
    m_pSat->setCurrentPart(1);
    //HG: Turning on incremental mode.
    //HG: This enables the use of
    //HG: selectors to speed up SAT solving
    m_pSat->setIncrementalMode();
  }

  /// Mark currently unmarked clauses as belonging to partition nPart
  void markPartition(unsigned nPart) {
    AVY_ASSERT(nPart > 0);
    if (nPart > m_nParts)
      m_nParts = nPart;
    m_pSat->setCurrentPart(nPart);
    LOG("glucose_dump", logs() << "c partition " << nPart << "\n";);
  }

  void reserve(int nVars) {
    while (m_pSat->nVars() < nVars)
      m_pSat->newVar();
  }

  bool addUnit(int unit) {
    ::Glucose::Lit p = ::Glucose::toLit(unit);
    LOG("sat", logs() << "UNT: " << (::Glucose::sign(p) ? "-" : "")
                      << (::Glucose::var(p)) << " ";);
    m_Trivial = !m_pSat->addClause(p);
    return m_Trivial;
  }

  bool addClause(int *bgn, int *end) {
    LOG("sat", logs() << "NEW CLS: ";);
    ::Glucose::vec<::Glucose::Lit> cls;
    cls.capacity(end - bgn);
    for (int *it = bgn; it != end; ++it) {
      ::Glucose::Lit p = ::Glucose::toLit(*it);
      cls.push(p);

      LOG("sat", logs() << (::Glucose::sign(p) ? "-" : "")
                        << (::Glucose::var(p)) << " ";);
      LOG("glucose_dump", logs() << (::Glucose::sign(p) ? "-" : "")
                                 << (::Glucose::var(p) + 1) << " ";);
    }
    LOG("sat", logs() << "\n" << std::flush;);
    LOG("glucose_dump", logs() << " 0\n" << std::flush;);

    m_Trivial = !m_pSat->addClause(cls);
    return !m_Trivial;
  }

  bool addClause(int *bgn, int *end, int nameLit) {
    AVY_ASSERT(nameLit >= 0);
    LOG("sat", logs() << "NEW CLS: ";);
    ::Glucose::vec<::Glucose::Lit> cls;
    cls.capacity(1 + (end - bgn));
    for (int *it = bgn; it != end; ++it) {
      ::Glucose::Lit p = ::Glucose::toLit(*it);
      cls.push(p);

      LOG("sat", logs() << (::Glucose::sign(p) ? "-" : "")
                        << (::Glucose::var(p)) << " ";);
      LOG("glucose_dump", logs() << (::Glucose::sign(p) ? "-" : "")
                                 << (::Glucose::var(p) + 1) << " ";);
    }
    ::Glucose::Lit p = ::Glucose::toLit(nameLit);
    cls.push(~p);
    LOG("sat", logs() << (::Glucose::sign(~p) ? "-" : "") << (::Glucose::var(p))
                      << "\n"
                      << std::flush;);
    LOG("glucose_dump", logs() << (::Glucose::sign(~p) ? "-" : "")
                               << (::Glucose::var(p) + 1) << " 0\n"
                               << std::flush;);
    m_Trivial = !m_pSat->addClause(cls);
    return !m_Trivial;
  }

  void dumpCnf(std::string fname) {
    ::Glucose::vec<::Glucose::Lit> v;
    m_pSat->toDimacs(const_cast<char *>(fname.c_str()), v);
  }

  /// raw access to the sat solver
  ::Glucose::Solver *get() { return m_pSat; }

  /// true if the context is decided
  bool isSolved() { return m_Trivial || m_State || !m_State; }

  int core(int **out) {
    m_core.clear();
    m_core.resize(m_pSat->conflict.size());
    for (unsigned i = 0; i < m_pSat->conflict.size(); i++)
      m_core[i] = m_pSat->conflict[i].x;

    *out = &m_core[0];
    return m_core.size();
  }
  /// decide context with assumptions
  // boost::tribool solve (LitVector &assumptions, int maxSize = -1)
  avy::tribool solve(const IntVector &assumptions, int minElem = 0,int maxSize = -1) {
    AVY_ASSERT(minElem>=0 && minElem < assumptions.size());
    ScoppedStats __stats__("Glucose_solve");
    if (m_Trivial)
      return false;

    if (!m_pSat->okay())
      return false;

    ::Glucose::vec<::Glucose::Lit> massmp;
    massmp.capacity(assumptions.size());
    int max = assumptions.size();
    if (maxSize >= 0 && maxSize < max)
      max = maxSize;

    for (unsigned i = minElem; i < max; ++i) {
      ::Glucose::Lit p = ::Glucose::toLit(assumptions[i]);
      massmp.push(p);
      LOG("sat", logs() << "ASM: " << (::Glucose::sign(p) ? "-" : "")
                        << (::Glucose::var(p)) << " "
                        << "\n";);
    }
    ::Glucose::lbool res =
        m_pSat->solveLimited(massmp, m_Simplifier, !m_Simplifier);
    if (res == ::Glucose::lbool(true))
      return true;
    else if (res == ::Glucose::lbool(false))
      return false;
    return avy::tribool();
  }
  /// a pointer to the unsat core
  // int core (int **out) { return sat_solver_final (m_pSat, out); }

  /// decide current context
  avy::tribool solve() {
    ScoppedStats __stats__("ItpGlucose_solve");
    return m_pSat->solve(m_Simplifier, !m_Simplifier);
  }
  bool isTrivial() { return m_Trivial; }

  void setFrozen(int v, bool p) {} // m_pSat->setFrozen (v, p); }
  void markSelector(int v, bool p){
    m_pSat->setSelector(v,p);
    m_pSat->setFrozen(v,p);
  }

  /// Compute an interpolant. User provides the list of shared variables
  /// Variables can only be shared between adjacent partitions.
  /// fMcM == true for McMillan, and false for McMillan'
  Aig_Man_t *getInterpolant(lit bad, std::vector<Vec_Int_t *> &vSharedVars,
                            int nNumOfVars, bool fMcM = true);

  bool getVarVal(int v) {
    ::Glucose::Var x = v;
    return tobool(m_pSat->modelValue(x));
  }

  unsigned getNumOfConflicts() const { return m_pSat->conflicts; }

  void setBudget(int nBudget) {
    if (nBudget < 0)
      m_pSat->budgetOff();
    else
      m_pSat->setConfBudget(nBudget);
  }
};

} // namespace avy

#undef l_True
#undef l_False
#undef l_Undef

#endif /* _ITPSATSOLVER_H_ */
