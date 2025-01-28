/*
 * GlucoseItpSeq.h
 *
 *  Created on: Jan 20, 2014
 *      Author: yakir
 */

#ifndef GLUCOSE_ITP_SEQ_H_
#define GLUCOSE_ITP_SEQ_H_

#include "ItpSequence.h"
#include "aig/gia/gia.h"
#include "glucose/core/ProofVisitor.h"
#include "glucose/simp/SimpSolver.h"
#include <vector>

namespace avy {
template <> class ProofLoggingTrait<::Glucose::Solver> {
public:
  typedef ::Glucose::ProofVisitor ProofVisitor;
  typedef ::Glucose::Solver Solver;
  typedef ::Glucose::Var Var;
  typedef ::Glucose::Lit Lit;
  typedef ::Glucose::CRef CRef;
  typedef ::Glucose::Clause Clause;
  typedef ::Glucose::vec<int> IntVec;
  typedef ::Glucose::vec<IntVec> IntIntVec;
  typedef ::Glucose::vec<IntIntVec> VecIntIntVec;
  typedef ::Glucose::CMap<int> IntCMap;
  typedef ::Glucose::CMap<IntVec> CMapIntVec;
  typedef ::Glucose::vec<IntCMap> VecIntCMap;
  typedef ::Glucose::vec<CMapIntVec> VecCMapIntVec;
  typedef ::Glucose::Range Range;

  enum { CRef_Undef = ::Glucose::CRef_Undef };

  static inline Var var(Lit p) { return ::Glucose::var(p); }
  static inline bool sign(Lit p) { return ::Glucose::sign(p); }
};

typedef ItpSequence<::Glucose::Solver> GlucoseItpSeq;
typedef ItpSequence<::Glucose::SimpSolver> SimpGlucoseItpSeq;
} // namespace avy

#endif /* GLUCOSE_ITP_SEQ_H_ */
