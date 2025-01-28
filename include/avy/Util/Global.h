#ifndef _GLOBAL_H_
#define _GLOBAL_H_

#include <iostream>
#include <string>

/** Global variables */
namespace avy {
struct AvyParams {
  std::string fName;

  /** name of counterexample file */
  std::string cexFileName;

  /**Interpolantion sequence to use
     0 McMillan, 1 McMillan' */
  unsigned itp;

  /** Use new avy code */
  bool avy;

  /** verbosity level */
  unsigned verbosity;

  /** stutter instead of reseting to initial state*/
  bool stutter;

  /** shallow push at every iteration */
  bool shallow_push;

  /** reset global pdr cover before updating it */
  bool reset_cover;

  /** satminimize unsat core */
  bool min_core;

  /** use muser to minimize unsat core */
  bool min_muser;

  /** incrementally add clauses to solver **/
  bool incr;

  /** interface abstraction */
  bool abstraction;

  /** Make Tr0 special */
  bool tr0;

  /** Frame at which to start PDR */
  int pdr;

  /** minimize suffix of interpolation sequence */
  bool min_suffix;

  /** always use sat_solver1 */
  bool sat1;

  /** use minisat */
  bool minisat;

  /** use glucose */
  bool glucose;

  /** use cadical */
  bool cadical;

  /** use glucose for itp */
  bool glucose_itp;

  /** use minisat itp */
  bool minisat_itp;

  /** use cadical itp */
  bool cadical_itp;
  bool cadical_itp_minimize;
  bool cadical_itp_inprocessing;
  bool cadical_itp_minimizer_inprocessing;
  bool cadical_itp_minimizer_preprocessing;

  std::string certificate;

  /** enable pre-processing for the fist SAT-solver if available */
  bool sat_simp;

  /** enable pre-processing during interpolation (if available) */
  bool itp_simp;

  /** enable proof reordering for the second SAT-solver if available */
  bool proof_reorder;

  /** enable glucose incremental mode */
  bool glucose_inc_mode;

  /** by how much to increase BMC in each iteration */
  unsigned kStep;

  /** stick error output */
  bool stick_error;

  bool itp_simplify;

  unsigned maxFrame;

  /// maximum number of conflict during cube generalization
  unsigned genConfLimit;

  // Use optimized BMC
  bool opt_bmc;

  // Only add clauses in the COI to the solver
  bool coi;

  // Try and push lemmas
  bool quip;

  // abstraction for lemmas
  bool lemmaAbs;

  // muser deletes clauses from the last unrolling
  bool muser_min_suffix;

  // muser deletes clauses from the first unrolling
  bool muser_min_prefix;

  // turn off model rotation in muser
  bool muser_unset_mr_mode;

  /// number of extra frames to push past safe bound
  unsigned num_extra_frames;

  /// k-induction policy
  unsigned kind_policy;

  /// reverse order of abstraction after kind
  bool reverseSA;

  /// commit to an abstraction when doing min Core
  bool commitAbs;

  /// repeat k-inductive frame atleast minK times in the proof. if minK<0,
  /// repeat it as much as possible
  int minK;

  /// Stop searching for k-inductive frame once we reach a level N-kThr
  unsigned kThr;

  /// abstract only suffix after kind
  bool suffixSA;

  bool bmc_incremental_assignment;
};

std::ostream &operator<<(std::ostream &out, const AvyParams &p);

extern AvyParams gParams;

/** Output streams */

/// std out
inline std::ostream &outs() { return std::cout; }
/// std err
inline std::ostream &errs() { return std::cerr; }
/// log stream. use in LOG() macro.
inline std::ostream &logs() { return std::cerr; }
/// verbose
inline std::ostream &vout() { return std::cout; }
} // namespace avy

#define VERBOSE(LVL, CODE)                                                     \
  do {                                                                         \
    if (LVL <= ::avy::gParams.verbosity) { CODE; }                             \
  } while (0)

#endif /* _GLOBAL_H_ */
