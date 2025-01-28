#pragma once
#include "api/muser2_api.hh"
#include "avy/Util/Stats.h"
#include "avy/Util/AvyTribool.h"
#include "avy/Util/Global.h" //defines gParams
#include "AvyTypes.h" //lit and IntVector

namespace avy {
inline lit muser2_gid_to_lit(const ::muser2::gid &gid) {return static_cast<lit>(gid);}
inline muser2::gid lit_to_muser2_gid(const lit &lit) {return static_cast<muser2::gid>(lit);}

class Muser2 {
  std::unique_ptr<muser2> m_muser;
  bool m_muser_initialized;
  boost::dynamic_bitset<> m_used_gids;
  IntVector m_core;

  void setUsedAssumption(int nameLit) {
    if (nameLit <= 0) return;
    if (m_used_gids.size() <= nameLit)
      m_used_gids.resize(nameLit + 1);
    m_used_gids.set(nameLit);
  }

  bool isUsedAssumption (int nameLit) {
    if (nameLit < 0 || m_used_gids.size() <= nameLit) return false;
    return nameLit == 0 || m_used_gids[nameLit];
  }

  void initMuserRun() {
    if (!m_muser_initialized) m_muser->init_run();
    m_muser_initialized = true;
  }

public:
  Muser2(unsigned nVars) {reset(nVars);}
  virtual ~Muser2() {}

  void reset(int nVars) {
    m_used_gids.clear();
    m_core.clear();
    m_muser.reset(new muser2());

    m_muser->set_delete_unnecessary_groups(false);
    m_muser->set_finalize_necessary_groups(false);
    m_muser->set_verbosity(0, "MUSER:");
    int muserMode =  gParams.muser_min_suffix ? 0 : gParams.muser_min_prefix ? 3 : 4 ;
    m_muser->set_order(muserMode);
    if(gParams.muser_unset_mr_mode)
      m_muser->unset_mr_mode();
    m_muser->rm_rr_mode(true);

    m_muser->init_all();
    m_muser_initialized = false;
  }

  void setCpuTimeLimit(double limit) {m_muser->set_cpu_time_limit(limit);}

  /** Add background clause */
  bool addClause(int *bgn, int *end) {return addClause(bgn, end, 0);}

  /**
   * Add a named clause. The name literal might appear in the unsat
   * core.
   *
   * nameLit is an arbitrary fresh literal, not appearing in any other clauses.
   */
  bool addClause(int *bgn, int *end, int nameLit) {
    std::vector<muser2::LINT> cls;
    for (int *it = bgn; it != end; ++it) {
      int var = Abc_Lit2Var(*it);
      var = Abc_LitIsCompl(*it) ? -var : var;
      cls.push_back(var);
      LOG("muser", logs() << var << " ";);
    }
    LOG("muser", logs() << "{" << lit_to_muser2_gid(nameLit) << "} 0\n";);
    int groupId = lit_to_muser2_gid(nameLit);
    int r = m_muser->add_clause(cls, groupId);
    AVY_ASSERT(r == groupId);
    setUsedAssumption(nameLit);
    return true;
  }

  /**
      Solve with assumptions. Assumptions are asserted as unit
      literals (unless they are gids).

      This method can only be called once between calls to reset()
   */
  tribool solve(IntVector &assumptions, int maxSize = -1) {
    AVY_MEASURE_FN;
    int max = assumptions.size();
    if (maxSize > 0 && maxSize < max) max = maxSize;

    // convert assumptions to clauses, unless they are already group ids
    for (int a : assumptions) {
      if (!isUsedAssumption(a)) {
        addClause(&a, &a + 1, a);
      }
    }

    initMuserRun();
    switch (m_muser->test_sat()) {
    case 10: return true;
    case 20: return false;
    default: return tribool();
    }
  }

  /**
   * Returns an unsat core. Can be called directly (i.e., without call to solve)
   * if the current clause DB is known to be unsat
   */
  const IntVector &getUnsatCore() {
    initMuserRun();
    AVY_MEASURE_FN;
    int result = m_muser->compute_gmus();
    AVY_ASSERT(result >= 0);
    if (result != 0) VERBOSE(2, vout() << "Approximate core found \n");
    const std::vector<muser2::gid> &gmus = m_muser->gmus_gids();
    m_core.clear();
    for (auto gid : gmus) m_core.push_back(muser2_gid_to_lit(gid));

    return m_core;
  }
};
}
