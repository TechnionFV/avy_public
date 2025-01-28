#pragma once

#include "AvyTypes.h" //IntVector
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"
#include "avy/Util/AvyTribool.h"
#include "cadical.hpp"
#include <iostream>

namespace avy {
class Cadical {
  ::CaDiCaL::Solver *m_sat;
  bool m_Trivial;
  bool m_Simplifier;
  bool m_Incremental;
  IntVector m_Assumptions;

  IntVector m_core;
  tribool tobool(int s) {
    tribool r;
    if (s == 10)
      r = true;
    else if (s == 20)
      r = false;
    AVY_ASSERT(s == 0);
    return r;
  }

  int toDimacsLit(int lit) {
    int v = (lit >> 1);
    AVY_ASSERT(v > 0);
    return (lit & 1) ? -v : v;
  }

public:
  Cadical(unsigned nVars, bool simp = true, bool inc = false)
      : m_sat(NULL), m_Trivial(false), m_Simplifier(simp), m_Incremental(inc) {
    reset(nVars);
    (void)m_Incremental;
  }

  virtual ~Cadical() {
    if (m_sat) delete m_sat;
  }

  void reset(int nVars) {
    m_core.clear();
    if (m_sat) delete m_sat;
    m_sat = new ::CaDiCaL::Solver();

    //m_sat->proofLogging(false);
    //m_sat->setIncrementalMode();
    reserve(nVars);
  }


  void reserve(int nVars) {
    m_sat->reserve(nVars);
  }

  bool addUnit(int unit) {
    int l = toDimacsLit(unit);
    LOG("sat", logs() << "UNT: " << l << " ";);
    m_sat->clause(l);
    m_Trivial = m_sat->inconsistent();
    return !m_Trivial;
  }

  bool addClause(int *bgn, int *end) {
    LOG("sat", logs() << "NEW CLS: ";);
    std::vector<int> cls(end - bgn);
    for (int *it = bgn; it != end; ++it) {
      int l = toDimacsLit(*it);
      cls[it-bgn] = l;

      LOG("sat", logs() << l << " ";);
    }
    LOG("sat", logs() << "\n" << std::flush;);

    m_sat->clause(cls);
    return !m_sat->inconsistent();
  }

  bool addClause(int *bgn, int *end, int nameLit) {
    AVY_ASSERT(nameLit >= 0);
    LOG("sat", logs() << "NEW CLS: ";);
    std::vector<int> cls(1 + (end - bgn));
    for (int *it = bgn; it != end; ++it) {
      //cls.push_back(toDimacsLit(*it))
      cls[it-bgn] = toDimacsLit(*it);
      LOG("sat", logs() << *it << " ";);
    }
    //cls.push_back(-toDimacsLit(nameLit));
    cls[end-bgn] = -toDimacsLit(nameLit);
    LOG("sat", logs() << -nameLit << " \n" << std::flush;);
    
    m_sat->clause(cls);
    m_Trivial = m_sat->inconsistent();
    return !m_Trivial;
  }

  void dumpCnf(std::string fname) {
    m_sat->write_dimacs(const_cast<char *>(fname.c_str()), m_sat->vars());
  }

  void dumpCnf(std::string fname, IntVector &assumptions) {
    m_sat->write_dimacs(const_cast<char *>(fname.c_str()), m_sat->vars());
    int max = assumptions.size();
    for (unsigned i = 0; i < max; ++i) {
      
      
    }
    assert(false);
  }

  tribool solve(const IntVector &assumptions, int maxSize = -1) {
    ScoppedStats __stats__("CaDiCaL_solve");
    if (m_Trivial) return false;

    if ((m_sat->state() & CaDiCaL::VALID) == 0) return false;

    int max = assumptions.size();
    if (maxSize >= 0 && maxSize < max) max = maxSize;

    // Clear the last used assumptions.
    m_Assumptions.clear();
    m_Assumptions.resize(max);
    for (unsigned i = 0; i < max; ++i) {
      int l = toDimacsLit(assumptions[i]);
      LOG("sat", logs() << "ASM: " << l << " " << "\n";);
      m_sat->assume(l);
      // Store the AVY assumption
      m_Assumptions[i] = assumptions[i];
    }
    tribool res = tobool(m_sat->solve());
    return res;
  }

  int core(int **out) {
    m_core.clear();

    std::cout << "Status: " << m_sat->state() << "\n";
    for (unsigned i = 0; i < m_Assumptions.size(); i++) {
        int lit = m_Assumptions[i];
        if (m_sat->failed(toDimacsLit(lit)))
            m_core.push_back(lit);
    }

    *out = &m_core[0];
    return m_core.size();
  }

  tribool solve() { return tobool(m_sat->solve()); } 

  bool isTrivial() { return m_Trivial; }

  bool isEliminated(int v) { 
    int l = toDimacsLit(v);
    int var = abs(l);
    return m_sat->active() >= var; 
  }

  void setFrozen(int v, bool p) {
    int l = toDimacsLit(v);
    int var = abs(l);
    if (p) {
      m_sat->freeze(var);
    } else {
      m_sat->melt(var);
    }
    //m_sat->setSelector(v, p);
  }

  void setDecisionVar(int v, bool p) {
    //m_sat->setDecisionVar(v, p);
    assert(false);
  }

  void markSelector(int v, bool p){
    //m_sat->setSelector(v,p);
    //m_sat->setFrozen(v,p);
    assert(false);
  }

  tribool getVarVal(int v) {
    int l = toDimacsLit(toLit(v));
    int var = abs(l);
    AVY_ASSERT(m_sat->state() & CaDiCaL::SATISFIED);
    return m_sat->val(var) > 0;
    //assert(!m_sat->isEliminated(x));
  }

  void markPartition(int nPart) {}

  void setHints(std::vector<int> & hints) {
    for (auto v : hints) {
      int lit = toDimacsLit(v);
      m_sat->phase(lit);
      return;
      if (lit & 1) {
        m_sat->phase(lit);
      }
      else {
        m_sat->phase(-lit);
      }
    }
      //assert(false);
  }
};

} // namespace avy
