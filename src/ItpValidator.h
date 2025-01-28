#pragma once

#include "AigUtils.h"
#include "CnfUtils.h"

#include "Glucose.h"
#include "Unroller.h"
#include "AvyTrace.h"

#include "avy/Util/Utils.h"
#include "avy/Util/Stats.h"

namespace avy {
template <typename SatSolver = Glucose>
class ItpValidator {

  // -- optimize Tr during validation
  bool m_propagate;

public:
  ItpValidator(bool propagate) :
    m_propagate(propagate) {}

  void setPropagate(bool v) {m_propagate = v;}
  bool operator()(Aig_Man_t *itp, Aig_Man_t *Tr, AvyTrace &TraceMan,int lemmaLevel=-1);
};
}
