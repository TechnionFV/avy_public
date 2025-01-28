/*
 * MinisatItpSeq.h
 *
 *  Created on: Jan 20, 2014
 *      Author: yakir
 */

#ifndef MINISAT_ITP_SEQ_H_
#define MINISAT_ITP_SEQ_H_

#include "ApproxItp.h"
#include "ItpSequence.h"
#include "aig/gia/gia.h"
#include <vector>
// -- hack, needed by SimpSolver
#define l_True (lbool((uint8_t)0))
#define l_False (lbool((uint8_t)1))
#define l_Undef (lbool((uint8_t)2))
#include "core/ProofVisitor.h"
#include "simp/SimpSolver.h"
#undef l_True
#undef l_False
#undef l_Undef

namespace avy {

template <> class ProofLoggingTrait<::Minisat::Solver> {
public:
  typedef ::Minisat::ProofVisitor ProofVisitor;
  typedef ::Minisat::Solver Solver;
  typedef ::Minisat::Var Var;
  typedef ::Minisat::Lit Lit;
  typedef ::Minisat::CRef CRef;
  typedef ::Minisat::Clause Clause;
  typedef ::Minisat::vec<int> IntVec;
  typedef ::Minisat::vec<IntVec> IntIntVec;
  typedef ::Minisat::vec<IntIntVec> VecIntIntVec;
  typedef ::Minisat::CMap<int> IntCMap;
  typedef ::Minisat::CMap<IntVec> CMapIntVec;
  typedef ::Minisat::vec<IntCMap> VecIntCMap;
  typedef ::Minisat::vec<CMapIntVec> VecCMapIntVec;
  typedef ::Minisat::Range Range;

  enum { CRef_Undef = ::Minisat::CRef_Undef };

  // -- alternative definition if above will not work
  // enum { CRef_Undef = ::Minisat::RegionAllocator<uint32_t>::Ref_Undef };

  static inline Var var(Lit p) { return ::Minisat::var(p); }
  static inline bool sign(Lit p) { return ::Minisat::sign(p); }
};

template <> class ProofLoggingTrait<::Minisat::SimpSolver> {
public:
  typedef ::Minisat::ProofVisitor ProofVisitor;
  typedef ::Minisat::SimpSolver Solver;
  typedef ::Minisat::Var Var;
  typedef ::Minisat::Lit Lit;
  typedef ::Minisat::CRef CRef;
  typedef ::Minisat::Clause Clause;
  typedef ::Minisat::vec<int> IntVec;
  typedef ::Minisat::vec<IntVec> IntIntVec;
  typedef ::Minisat::vec<IntIntVec> VecIntIntVec;
  typedef ::Minisat::CMap<int> IntCMap;
  typedef ::Minisat::CMap<IntVec> CMapIntVec;
  typedef ::Minisat::vec<IntCMap> VecIntCMap;
  typedef ::Minisat::vec<CMapIntVec> VecCMapIntVec;
  typedef ::Minisat::Range Range;

  enum { CRef_Undef = ::Minisat::CRef_Undef };

  // -- alternative definition if above will not work
  // enum { CRef_Undef = ::Minisat::RegionAllocator<uint32_t>::Ref_Undef };

  static inline Var var(Lit p) { return ::Minisat::var(p); }
  static inline bool sign(Lit p) { return ::Minisat::sign(p); }
};

typedef ItpSequence<::Minisat::Solver> MinisatItpSeq;
typedef ItpSequence<::Minisat::SimpSolver> SimpMinisatItpSeq;

} // namespace avy

#endif /* MINISAT_ITP_SEQ_H_ */
