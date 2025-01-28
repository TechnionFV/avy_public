#pragma once
#include "SafetyVC2.h"
#include "Unroller.h"
#include "boost/dynamic_bitset.hpp"
#include "boost/range/algorithm/copy.hpp"
#include <string>

#include "AvyTypes.h" //IntVector
#include "ItpGlucose.h"
#include "ItpCadical.h"
#include "ItpMinisat.h"
#include "Muser2.h"

namespace avy {
template <typename SatSolver> class UnsatCoreComputer {
  /// Tracks the latest core
  IntVector m_Core;

  /// bitset index over m_Core: m_bCore.test(x) is true iff x is in m_Core
  boost::dynamic_bitset<> m_bCore;

  Unroller<SatSolver> *m_Unroller;
  SatSolver *m_SatSolver;

  /// Muser instance for core computation
  Muser2 *m_Muser;

  /// VC to generate unrolling
  SafetyVC2 *m_Vc;

  /// The bad literal in the last frame
  lit m_badLit;

  /// level relative to which the property is k-inductive
  unsigned m_lemmaLevel = 0;

  /// klevel[n]=k means that k is the largest frame such that kBMC(n, k) is
  /// UNSAT. k < n means that kBMC(n, n) is SAT
  IntVector klevel;

  /// Something about abstraction
  boost::dynamic_bitset<> committedAbs;

public:
  UnsatCoreComputer(Unroller<SatSolver> *unroller, SatSolver *sat,
                    Muser2 *muser, SafetyVC2 *vc)
      : m_Unroller(unroller), m_SatSolver(sat), m_Muser(muser), m_Vc(vc) {}

  unsigned getLemmaLevel() const { return m_lemmaLevel; }

  /// \brief Computes an unsat-core over assumptions of current unroller
  ///
  /// \return Reference to the core. The reference is valid until next call to
  /// \p computeUNSATCore
  IntVector &computeUNSATCore() {
    m_Core.clear();
    m_bCore.reset();
    m_badLit = m_Unroller->getBadLit();
    klevel.clear();
    for (int i = 0; i < m_Unroller->frame() + 1; i++) {
      klevel.push_back(i - 1);
    }
    VERBOSE(2, vout() << "Assumption size: " << m_Unroller->getAssumps().size()
                      << "\n";);

    // -- compute core using algorithm specified in global parameters
    // TODO dynamic dispatch
    tribool res;
    {
      ScoppedStats _s_("core_computation");
      if (gParams.lemmaAbs) {
        // use gParams.minSuffix to avoid having additional TRs in the formula
        // that is fed into the sat solver
        res = computeKinductiveCore();
      } else if (gParams.min_muser) {
        res = computeMuserCore();
      } else if (gParams.min_suffix) {
        res = computeMinSuffix();
      } else {
        res = computeMinCore(m_Unroller->getAssumps());
      }
    }
    VERBOSE(2, vout() << " core size: " << m_Core.size() << "\n";);

    // build bitset index for the core
    for (unsigned i = 0; i < m_Core.size(); ++i) {
      unsigned int a = m_Core[i];
      if (m_Core[i] == m_badLit) continue;
      if (m_bCore.size() <= a) m_bCore.resize(a + 1);
      m_bCore.set(a);
    }

    /// some core-computation algorithm leave the sat-solver in sat state
    /// for these cases, re-compute unsat
    if (res) {
      ScoppedStats _s_("itp_solve");
      res = m_SatSolver->solve(m_Core, 0, m_Core.size());
    }

    AVY_ASSERT(!res);
    return m_Core;
  }

private:
  /// \brief Returns true if literal \p l is in the committed index
  bool isCommitted(lit l) {
    return (committedAbs.size() > l && committedAbs.test(l));
  }
  /// \brief Mark literal \p l as committed
  void markCommitted(lit l) {
    if (committedAbs.size() <= l) committedAbs.resize(l + 1);
    committedAbs.set(l);
  }

  /// \brief Computes minimal core in some way
  ///
  /// \param[in] assumps assumptions that are minimized
  tribool computeMinCoreIncr(const IntVector &assumps) {
    AVY_MEASURE_FN;
    AVY_ASSERT(assumps.size() <= m_Unroller->getAssumps().size() &&
               assumps.size() > 0);
    unsigned numSatQueries = 0, numSkipped = 0;

    // -- get last conflict from sat solver
    int *pCore = nullptr;
    int coreSz = m_SatSolver->core(&pCore);

    // a core is the negation of the last conflict
    // TODO: move negation into SatSolver interface
    m_Core.assign(pCore, pCore + coreSz);
    for (lit &p : m_Core) p = lit_neg(p);

    // naive unsat-core loop. Remove literal and check if still unsat
    tribool res = false;
    for (unsigned int i = 0; m_Core.size() > 1 && i < assumps.size(); ++i) {
      lit a = assumps[i];
      // if the abstraction has already been committed, don't try to remove it
      if (isCommitted(a)) {
        // XXX: Assumes that assumption literals do not change
        // throughout different unrollings. This is fragile and is not always
        // true
        numSkipped++;
        continue;
      }

      auto pos = std::find(m_Core.begin(), m_Core.end(), a);
      // check whether a already been removed
      if (pos == std::end(m_Core)) continue;
      *pos = m_Core.back();
      res = m_SatSolver->solve(m_Core, 0, m_Core.size() - 1);
      numSatQueries++;
      if (!res) {
        // use SAT core in next iteration
        coreSz = m_SatSolver->core(&pCore);
        m_Core.assign(pCore, pCore + coreSz);
        for (lit &p : m_Core) p = lit_neg(p);
        // add to committed abstractions
        markCommitted(a);
      } else {
        // SAT, put back the literal
        *pos = a;
      }
    }

    Stats::uset("numSatQueriesInMinCore", numSatQueries);
    Stats::uset("assumpsTried", assumps.size());
    Stats::uset("numSkipped", numSkipped);
    return res;
  }

  /// \brief Compute minimal core of given assumptions
  ///
  /// \return the last result from the sat-solver
  tribool computeMinCore(const IntVector &assumps) {
    AVY_MEASURE_FN;
    AVY_ASSERT(assumps.size() <= m_Unroller->getAssumps().size() &&
               assumps.size() > 0);

    unsigned numSatQueries = 0;

    int *pCore = nullptr;
    int coreSz = m_SatSolver->core(&pCore);
    m_Core.assign(pCore, pCore + coreSz);
    for (lit &p : m_Core) p = lit_neg(p);

    tribool res = false;
    for (unsigned int i = 0; m_Core.size() > 1 && i < assumps.size(); ++i) {
      lit a = assumps[i];
      auto pos = std::find(std::begin(m_Core), std::end(m_Core), a);
      if (pos == std::end(m_Core)) continue;
      *pos = m_Core.back();
      res = m_SatSolver->solve(m_Core, 0, m_Core.size() - 1);
      numSatQueries++;
      if (!res) {
        // use SAT core in next iteration
        coreSz = m_SatSolver->core(&pCore);
        m_Core.assign(pCore, pCore + coreSz);
        for (lit &p : m_Core) p = lit_neg(p);
      } else {
        // SAT, put back the literal
        *pos = a;
      }
    }
    Stats::uset("satQueriesInMinCore", numSatQueries);
    Stats::uset("assumpsTried", assumps.size());
    return res;
  }
  tribool computeMinSuffix() {
    AVY_MEASURE_FN;
    // -- minimize suffix
    // this is the not the flow for combining lemmaAbs and minSuffix
    AVY_ASSERT(!gParams.lemmaAbs);
    IntVector assumps;
    assumps.push_back(m_badLit);
    assumps.reserve(m_Unroller->getAssumps().size());
    int i;
    for (i = m_Unroller->frame(); i >= 0; --i) {
      boost::copy(m_Unroller->getFrameAssumps(i), std::back_inserter(assumps));
      tribool res = m_SatSolver->solve(assumps);
      if (!res) {
        VERBOSE(2, if (i > 0) vout() << "Killed " << i << " of prefix\n";);
        break;
      }
    }
    // should not be always SAT
    AVY_ASSERT(i >= 0);
    // does not require re-solving for interpolants
    return false;
  }
  tribool computeMuserCore() {
    AVY_MEASURE_FN;
    // muser needs to be reset after every call
    AVY_ASSERT(!gParams.incr);
    // copies core vector
    m_Core = m_Muser->getUnsatCore();
    // require resolving for itp generation
    return true;
  }
  // BMC query starting at cycle n and using lemmas of frame greater or equal
  // than k  assumes that m_Core already contains the bad literal and any other
  // required assumptions
  tribool kBMC(unsigned n, unsigned k) {
    Stats::count("satQueries");
    AVY_ASSERT(k >= n);
    m_Unroller->appendAssumpsInRange(n, m_Unroller->frame(), k, m_Vc->getSize(),
                                     m_Core);
    return m_SatSolver->solve(m_Core);
  }
  // computes the minimum suffix when lemmas are abstracted
  // assumes that m_Core already contains the bad literal and any other
  // required assumptions
  int computeMinSuffixkInd() {
    size_t absSz = m_Core.size();
    tribool res;
    int i;
    // minimize suffix
    for (i = m_Unroller->frame() - 1; i >= 0; --i) {
      m_Core.resize(absSz);
      res = kBMC(i, i);
      // suffix found
      if (!res) return i;
    }
    AVY_ASSERT(false);
    return 0;
  }
  // top_down : top down approach to finding SEL
  // top_down finds the largest frame relative to which the property is
  // k-inductive with the option gParams.minK, it can find the smallest suffix
  // with which this happens as well HOW : top_down finds the largest k for
  // which kBMC(0,k) is UNSAT and then tries to minimize the suffix according to
  // gParams.minK assumes that m_Core already contains the bad literal and any
  // other required assumptions
  tribool top_down() {
    // Find largest k-induction level first,
    // then minimize the suffix
    unsigned nFrame = m_Unroller->frame();
    size_t absSz = m_Core.size();
    tribool res = true;

    for (int kindLevel = nFrame - 1; res && kindLevel >= 0; kindLevel--) {
      Stats::resume("top-down-phase1");
      // reset core back to abstraction
      m_Core.resize(absSz);
      res = kBMC(0, kindLevel);
      if (!res) {
        // k-inductive core generated
        VERBOSE(2, vout() << nFrame << "-inductive relative to frame "
                          << kindLevel << "\n");
        m_lemmaLevel = kindLevel;
        Stats::stop("top-down-phase1");
        unsigned minLevel = m_Unroller->findMinLevel(m_Core);
        AVY_ASSERT(minLevel <= m_lemmaLevel);
        unsigned depthOfInduction = m_lemmaLevel - minLevel + 1;
        // gParams.minK >= 0 : Minimize suffix. minimum length of suffix is
        // nFrame + 1 - ( kindLevel + gParams.minK ) i.e repeat F_kindLevel
        // atleast minK times in the proof
        // gParams.minK <0   : don't minimize suffix
        if (gParams.minK < 0 || kindLevel - gParams.minK < 0 ||
            depthOfInduction <= gParams.minK) {
          Stats::avg("kInductiveDepth", depthOfInduction);
          return false;
        }
        // minimize suffix in the k-inductive core
        for (int i = m_lemmaLevel - gParams.minK; i >= minLevel; --i) {
          ScoppedStats loopStats("minimizingSuffix");
          depthOfInduction = m_lemmaLevel - i + 1;
          // Reset core but do not modify assumption literals of abstraction
          m_Core.resize(absSz);
          res = kBMC(i, m_lemmaLevel);
          AVY_ASSERT(i != minLevel || !res);
          if (!res) {
            Stats::avg("kInductiveDepth", depthOfInduction);
            // found minimum suffix
            VERBOSE(2, vout() << nFrame - i << "-inductive at frame "
                              << m_lemmaLevel << "\n");
            return false;
          }
        }
      }
    }
    AVY_ASSERT(!res);
    return res;
  }
  /// bottom_up : bottom up approach to finding SEL
  tribool bottom_up() {
    unsigned nFrame = m_Unroller->frame();
    size_t absSz = m_Core.size();
    m_lemmaLevel = computeMinSuffixkInd();
    tribool res = false;
    AVY_ASSERT(m_lemmaLevel < nFrame);
    unsigned k = 1;
    unsigned l = 2, j = m_lemmaLevel + 1;
    while (l <= (j + 1) && j <= nFrame - 1) {
      if (gParams.kThr > 0 && l > gParams.kThr) break;
      // reset core back to abstraction
      m_Core.resize(absSz);
      AVY_ASSERT(j - l + 1 >= 0);
      res = kBMC(j - l + 1, j);
      if (res) {
        l++;
      } else {
        j = m_Unroller->findMinFrame(m_Core);
        AVY_ASSERT(j <= nFrame - 1);
        m_lemmaLevel = j;
        k = l;
        j++;
      }
    }
    Stats::avg("kInductiveDepth", k);
    if (res) {
      m_Core.resize(absSz);
      return kBMC(m_lemmaLevel - k + 1, m_lemmaLevel);
    } else
      return res;
  }
  /// \brief Compute k-inductive unsat core
  tribool computeKinductiveCore() {
    AVY_MEASURE_FN;
    AVY_ASSERT(!(gParams.min_suffix && gParams.abstraction));
    unsigned nFrame = m_Unroller->frame();
    m_lemmaLevel = 0;

    // if we want to compute abstraction, load those assumptions into m_Core.
    // Minimize them after computing k-inductive core
    if (gParams.abstraction) m_Core = m_Unroller->getAbstractedLiterals();

    m_Core.push_back(m_badLit);

    // get the assumption literal for the last frame. This literal should not be
    // removed. This is because the base case for k-induction does not include
    // this frame.
    if (m_Vc->getPreCond(nFrame).size() > 0) {
      m_Unroller->appendAssumpsInRange(nFrame, nFrame + 1, nFrame,
                                       m_Vc->getSize(), m_Core);
    }

    // for k-induction we minimize m_Core[absSz+1..] and for abstraction,
    // we minimize m_Core[0..absSz]
    size_t absSz = m_Core.size();

    tribool res = true;
    switch (gParams.kind_policy) {
    case sel_algthms::top_down: {
      res = top_down();
      break;
    }
    case sel_algthms::bot_up: {
      res = bottom_up();
      break;
    }
    }
    Stats::avg("kInductiveSuffix", m_lemmaLevel);

    // AG: At this point we need to check whether kindLevel can be increased
    // AG: at the cost of increasing the length of the unrolling.
    // AG: And then the procedure repeats.

    // AG: The code below needs refactoring. Will be impossible to
    // describe in a pseudocode

    // after finding k-inductive core, find circuit abstraction
    if (gParams.abstraction && absSz > 1) {
      // AG: m_lemmaLevel is not the suffix! At least not if this is
      // implementing the the algorithm we discussed

      // try to minimize assumptions in the suffix of the unrolling or in the
      // whole unrolling
      int startingLevel = gParams.suffixSA ? m_lemmaLevel : 0;
      // get all latch assumptions in and above startingLevel
      IntVector suffixAssumptions =
          m_Unroller->getAbstractedLiterals(startingLevel);
      if (gParams.reverseSA) {
        std::reverse(suffixAssumptions.begin(), suffixAssumptions.end());
      }

      // AG: The mechanism for committing to abstraction needs to be rethought
      // commit to an abstraction
      if (gParams.commitAbs)
        return computeMinCoreIncr(suffixAssumptions);
      else
        return computeMinCore(suffixAssumptions);
    }
    return res;
  }
};
}; // namespace avy
