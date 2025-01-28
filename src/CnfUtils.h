#pragma once

#include "avy/AvyAbc.h"

#include "sat/cnf/cnf.h"
#include <memory>

namespace avy {
using namespace avy::abc;

/// smart pointer for Cnf_Dat_t.
typedef std::shared_ptr<Cnf_Dat_t> CnfPtr;
namespace {
struct cnf_deleter {void operator()(Cnf_Dat_t *p) {if (p) Cnf_DataFree(p);}};
} // namespace

inline CnfPtr cnfPtr(Cnf_Dat_t *p) { return CnfPtr(p, cnf_deleter()); }

/// Lifts Cnf for the lifetime of the instance
class ScoppedCnfLift {
  CnfPtr &m_Cnf;
  int m_nOffset;

public:
  ScoppedCnfLift(CnfPtr &cnf, int nOffset) : m_Cnf(cnf), m_nOffset(nOffset) {
    Cnf_DataLift(&*m_Cnf, m_nOffset);
  }
  ~ScoppedCnfLift() { Cnf_DataLift(&*m_Cnf, -m_nOffset); }
};

Cnf_Dat_t *AvyCnf_Derive(Aig_Man_t * pAig, int nOutputs );
}
