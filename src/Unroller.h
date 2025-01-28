#ifndef _UNROLLER_H_
#define _UNROLLER_H_

#include <cassert>

#include "misc/vec/vec.h"
#include "sat/cnf/cnf.h"
#include <algorithm>
#include <unordered_map>
#include <vector>

#include "boost/dynamic_bitset.hpp"

#include "AvyTypes.h"
#include "CnfUtils.h"
#include "Muser2.h"
#include "avy/AvyAbc.h"
#include "avy/Util/Global.h"

// SVAR : starting varible
// starting from 1 to avoid variable 0. This is because muser uses the DIMACS
// way of representing variables and therefore can't use variable 0
#define SVAR 1

namespace avy {
template <typename SatSolver> class Unroller {
  /// smart pointer for Cnf_Dat_t.
  SatSolver *m_pSolver;
  Muser2 *m_muser;
  unsigned m_nVars;
  unsigned m_nFrames;
  /// Primary Inputs, by frame
  std::vector<avy::abc::Vec_Int_t *> m_vPrimaryInputs;
  /// Inputs, by frame
  std::vector<avy::abc::Vec_Int_t *> m_vInputs;
  /// Outputs, by frame
  std::vector<avy::abc::Vec_Int_t *> m_vOutputs;
  /// All assumptions
  IntVector m_Assumps;

  /// a per-frame, per-wire, flags whether glue clauses have been asserted
  std::vector<IntVector> m_Glued;
  /// assumption variable per frame that disconnects all the glue wires
  IntVector m_GlueVars;
  /// glue variables per-wire per frame
  std::vector<IntVector> m_vAbstractedVariables;
  /**
   * Start of frame assumptions in m_Assumps
   * m_Assumps[i] is the start of assumptions of frame i in m_Assumps
   */
  std::vector<unsigned> m_FrameAssump;

  /*
   * For each level, maintain a map of levels to assumption literals of those
   * levels
   */
  std::unordered_map<unsigned, std::unordered_map<unsigned, lit>>
      m_mlevelToAssumps;

  /// stores the assignment to assumption literals in UNSAT core. Used to
  /// re-generate CNF formula for interpolation
  boost::dynamic_bitset<> *m_pEnabledAssumps;

  /// keeps track of which all literals are in m_Assumps. Used to prevent
  /// duplicates
  boost::dynamic_bitset<> m_pEnabledAssumpLit;

  bool m_fWithAssump;
  /// Literal for Bad output
  lit m_BadLit;

public:
  Unroller(SatSolver &s, Muser2 *m = nullptr, bool fWithAssump = false)
      : m_pSolver(&s), m_nVars(SVAR), m_nFrames(0), m_pEnabledAssumps(0),
        m_fWithAssump(fWithAssump), m_BadLit(-1) {
    m_muser = m;
    newFrame();
  }

  bool withAssumps() { return m_fWithAssump; }

  ~Unroller() { reset(NULL, nullptr); }

  void setBadLit(lit bad) { m_BadLit = bad; }
  lit getBadLit() {
    AVY_ASSERT(m_BadLit >= 0);
    return m_BadLit;
  }

  bool pushBadUnit() {
    lit b = getBadLit();
    AVY_ASSERT(m_FrameAssump.size() > 0);
    if (m_muser != nullptr) m_muser->addClause(&b, &b + 1);
    return m_pSolver->addClause(&b, &b + 1);
  }

  void setEnabledAssumps(boost::dynamic_bitset<> &v) { m_pEnabledAssumps = &v; }

  /** Reset everything */
  void reset(SatSolver *solver, Muser2 *muser) {
    for (Vec_Int_t *vVec : m_vPrimaryInputs) Vec_IntFree(vVec);
    m_vPrimaryInputs.clear();
    for (Vec_Int_t *vVec : m_vInputs) Vec_IntFree(vVec);
    m_vInputs.clear();

    for (Vec_Int_t *vVec : m_vOutputs) Vec_IntFree(vVec);
    m_vOutputs.clear();

    m_Assumps.clear();
    m_FrameAssump.clear();

    m_GlueVars.clear();
    m_vAbstractedVariables.clear();

    m_Glued.clear();

    m_nVars = SVAR;
    m_nFrames = 0;
    m_pEnabledAssumps = NULL;
    m_mlevelToAssumps.clear();
    m_pEnabledAssumpLit.reset();

    if (solver) {
      m_pSolver = solver;
      newFrame();
    }
    if (muser) m_muser = muser;
  }
  void resetGluedVars(int frame) { m_Glued.at(frame).clear(); }

  void resetLastFrame() {
    Vec_IntClear(m_vInputs.back());
    Vec_IntClear(m_vPrimaryInputs.back());
    m_Glued.back().clear();
    // -- Deletes the assumption literal of bad from previous unrolling
    if (!m_FrameAssump.empty()) {
      AVY_ASSERT(m_Assumps.size() >= m_FrameAssump.back());
      while (m_FrameAssump.back() != m_Assumps.size()) {
        AVY_ASSERT(m_pEnabledAssumpLit.test(m_Assumps.back()));
        m_pEnabledAssumpLit.reset(m_Assumps.back());
        m_Assumps.pop_back();
      }
    }
    // -- Reset glueVars from last frame. This is required in
    // -- incr mode where the last frame is the bad frame.
    if (!m_GlueVars.empty()) m_GlueVars.pop_back();
    m_pSolver->markPartition(frame() + 1);
    // preconditions are reset at every frame
    // because of pushing, the frames may have changed
    // this leads to incorrect mapping of lemma levels to assumptions
    // among pushed lemmas
    m_mlevelToAssumps.clear();
    if (gParams.lemmaAbs) {
      m_pEnabledAssumpLit.reset();
      m_Assumps.clear();
      // m_FrameAssump is not required when we do lemmaAbs
      m_FrameAssump.clear();
      if (gParams.abstraction) {
        m_Assumps = getAbstractedLiterals();
        for (lit a : m_Assumps) { markAssumpAdded(a); }
      }
      if (gParams.min_suffix) {
        for (lit a : m_GlueVars) { addAssump(toLit(a)); }
      }
    }
  }

  /** allocate a fresh solver variable */
  unsigned freshVar() {
    unsigned v = m_nVars++;
    m_pSolver->reserve(m_nVars);
    return v;
  }

  /** allocate a block of fresh variables */
  unsigned freshBlock(unsigned b) {
    unsigned v = m_nVars;
    m_nVars += b;
    m_pSolver->reserve(m_nVars);
    return v;
  }

  /// register literal as an assumption
  void addAssump(lit a) {
    // HG : prevent duplicates in m_Assumptions
    // HG : could prevent it by checking in the client side
    // HG : but then addNamedClause cannot be used throughout
    // HG : Not using a set since we need to maintain order
    // HG : for min-suffix unsat core computation
    AVY_MEASURE_FN;
    if (m_pEnabledAssumpLit.size() > a && m_pEnabledAssumpLit.test(a)) return;
    m_Assumps.push_back(a);
    markAssumpAdded(a);
  }

  /// return all assumptions
  const IntVector &getAssumps() { return m_Assumps; }

  /// return assumptions for a given frame
  std::pair<int *, int *> getFrameAssumps(unsigned nFrame) {
    AVY_ASSERT(nFrame < m_FrameAssump.size());
    int *bgn = &m_Assumps[0] + m_FrameAssump.at(nFrame);
    int *end = &m_Assumps[0];
    if (nFrame + 1 == m_FrameAssump.size())
      end += m_Assumps.size();
    else
      end += m_FrameAssump.at(nFrame + 1);
    return std::make_pair(bgn, end);
  }

  /// current frame
  unsigned frame() const { return m_nFrames - 1; }
  /// total number of frames
  unsigned frames() const { return m_nFrames; }

  void newFrame() {
    m_nFrames++;
    m_vPrimaryInputs.push_back(Vec_IntAlloc(16));
    m_vInputs.push_back(Vec_IntAlloc(16));
    m_vOutputs.push_back(Vec_IntAlloc(16));
    m_FrameAssump.push_back(m_Assumps.size());
    m_Glued.push_back(IntVector());
    m_vAbstractedVariables.push_back(IntVector());
    m_pSolver->markPartition(m_nFrames);
  }

  void addPrimaryInput(int in) {
    avy::abc::Vec_IntPush(m_vPrimaryInputs.at(frame()), in);
  }

  int getPrimaryInput(unsigned nFrame, int nNum) {
    return avy::abc::Vec_IntEntry(m_vPrimaryInputs.at(nFrame), nNum);
  }

  avy::abc::Vec_Int_t *getPrimaryInputs(unsigned nFrame) {
    return m_vPrimaryInputs.at(nFrame);
  }

  void addInput(int in) { avy::abc::Vec_IntPush(m_vInputs.at(frame()), in); }

  int getInput(unsigned nFrame, int nNum) {
    return avy::abc::Vec_IntEntry(m_vInputs.at(nFrame), nNum);
  }

  avy::abc::Vec_Int_t *getInputs(unsigned nFrame) {
    return m_vInputs.at(nFrame);
  }

  void addOutput(int out) {
    avy::abc::Vec_IntPush(m_vOutputs.at(frame()), out);
  }

  int getOutput(unsigned nFrame, int nNum) {
    return avy::abc::Vec_IntEntry(m_vOutputs.at(nFrame), nNum);
  }

  avy::abc::Vec_Int_t *getOutputs(unsigned nFrame) {
    return m_vOutputs.at(nFrame);
  }
  std::vector<avy::abc::Vec_Int_t *> &getAllOutputs() { return m_vOutputs; }

  void setFrozenOutputs(unsigned nFrame, bool v) {
    avy::abc::Vec_Int_t *outputs = m_vOutputs[nFrame];
    int out, i;
    Vec_IntForEachEntry(outputs, out, i) {
      if (out == -1) continue;
      lit l = toLit(out);
      m_pSolver->setFrozen(lit_var(l), v);
    }
  }

  void setFrozenInputs(unsigned nFrame, bool v) {
    avy::abc::Vec_Int_t *inputs = m_vInputs[nFrame];
    int out, i;
    Vec_IntForEachEntry(inputs, out, i) {
      if (out == -1) continue;
      lit l = toLit(out);
      m_pSolver->setFrozen(lit_var(l), v);
    }
    inputs = m_vPrimaryInputs[nFrame];
    Vec_IntForEachEntry(inputs, out, i) {
      if (out == -1) continue;
      lit l = toLit(out);
      m_pSolver->setFrozen(lit_var(l), v);
    }
  }

  void setFrozenVars(const std::vector<int>& vars, bool v) {
    for (auto var : vars) {
      if (var == -1) continue;
      lit l = toLit(var);
      m_pSolver->setFrozen(lit_var(l), v);
    }
  }

  void setDecisionVars(const std::vector<int>& vars, bool v) {
    for (auto var : vars) {
      if (var == -1) continue;
      lit l = toLit(var);
      m_pSolver->setDecisionVar(lit_var(l), v);
    }
  }

  /** Add clause to solvers */
  tribool addClause(avy::abc::lit *beg, avy::abc::lit *end,
                           int nFrame = -1) {
    if (nFrame >= 0) { m_pSolver->markPartition(nFrame + 1); }
    if (m_muser) m_muser->addClause(beg, end); // add it permanently
    return m_pSolver->addClause(beg, end);
  }

  /** Add named clause to solvers. The names are stored as assumptions */
  tribool addNamedClause(avy::abc::lit *beg, avy::abc::lit *end,
                                int nFrame = -1, avy::abc::lit nameLit = -1) {
    if (nFrame >= 0) { m_pSolver->markPartition(nFrame + 1); }
    if (m_muser) m_muser->addClause(beg, end, nameLit);
    if (nameLit >= 0) addAssump(nameLit);
    return m_pSolver->addClause(beg, end, nameLit);
  }

  /// Add CNF db to the solver(s)
  /// The sat solver is in the correct partition.
  tribool addCnf(Cnf_Dat_t *pCnf) {
    tribool res = true;
    for (int i = 0; i < pCnf->nClauses; ++i)
      res = res && addClause(pCnf->pClauses[i], pCnf->pClauses[i + 1]);
    return res;
  }

  /// return true if the given assumption literal is true
  tribool eval(lit a) {
    tribool res;

    if (!m_pEnabledAssumps) return res;
    if (a >= ((lit)m_pEnabledAssumps->size())) return false;
    return m_pEnabledAssumps->test(a);
  }

  void glueOutIn(int nFrame = -1) {
    unsigned f = frame();
    if (nFrame != -1) {
      f = nFrame;
      m_pSolver->markPartition(f + 1);
    }
    if (gParams.abstraction)
      glueOutIn2(f);
    else
      glueOutIn1(f);
  }

  /** Add glue clauses between current Inputs and previous frame outputs */
  void glueOutIn1(unsigned nFrame) {

    AVY_ASSERT(m_nFrames > 1);
    AVY_ASSERT(Vec_IntSize(m_vOutputs.at(nFrame - 1)) ==
               Vec_IntSize(m_vInputs.at(nFrame)));

    lit Lit[2];

    int out, i;

    Vec_Int_t *ins = m_vInputs.at(nFrame);
    lit aLit;
    tribool aVal;
    IntVector &glued = m_Glued[nFrame];
    if (m_fWithAssump) {
      int a;
      if (m_GlueVars.size() <= nFrame) {
        a = freshVar();
        m_GlueVars.push_back(a);
      } else
        a = m_GlueVars[nFrame];

      aLit = toLit(a);
      aVal = eval(aLit);

      if (!aVal)
        // -- assumption is set to false
        // do not add any clause in this frame
        return;
    }

    if (glued.size() == 0) glued.resize(Vec_IntSize(ins), -1);
    AVY_ASSERT(glued.size() == Vec_IntSize(ins));
    Vec_IntForEachEntry(m_vOutputs.at(nFrame - 1), out, i) {
      if (out == -1 || glued[i] != -1) continue;
      glued[i] = 1;
      Lit[0] = toLit(out);
      Lit[1] = toLitCond(Vec_IntEntry(ins, i), 1);
      addGlueClause(Lit, Lit + 2, nFrame, aLit, aVal);
      Lit[0] = lit_neg(Lit[0]);
      Lit[1] = lit_neg(Lit[1]);
      addGlueClause(Lit, Lit + 2, nFrame, aLit, aVal);
    }
  }
  /// get assumption literals for output latches in frames [lvl,NFrame)
  IntVector getAbstractedLiterals(unsigned lvl = 0) {
    AVY_ASSERT(m_vAbstractedVariables.size() > 0);
    AVY_ASSERT(lvl < m_vAbstractedVariables.size());
    IntVector temp;
    temp.reserve((m_vAbstractedVariables.size() - lvl) *
                 Vec_IntSize(m_vInputs[0]));
    // m_vAbstractedVariables[i] is the assumps for outputs at i-1
    // m_vAbstractedVariables[0] is always empty
    for (unsigned i = lvl + 1; i < m_vAbstractedVariables.size(); i++) {
      for (int s : m_vAbstractedVariables[i]) temp.push_back(toLit(s));
    }
    return temp;
  }

  /// appends assumption literals of clauses of depth [minFrame,maxFrame) in
  /// levels [minlevel,maxLevel)
  /// L1 |               |
  ///----|---------------|----minFrame=2
  /// L2 |  L2           |
  /// L3 |  L3   L3      |
  ///----|---------------|--- maxFrame=4
  /// L4 |  L4   L4   L4 |
  /// minLevel=1       maxLevel=4
  /// AssumpsInRange(1,4,2,4) = L2
  ///                           L3 L3
  void appendAssumpsInRange(unsigned minLevel, unsigned maxLevel,
                            unsigned minFrame, unsigned maxFrame,
                            IntVector &literals) {
    AVY_ASSERT(maxLevel > minLevel);
    AVY_ASSERT(minFrame >= minLevel);
    AVY_ASSERT(maxFrame >= minFrame);
    for (int i = maxLevel - 1; i >= minLevel && i >= 0; --i) {
      int lb = minFrame < i ? i : minFrame;
      appendAssumpForlevel(i, lb, maxFrame, literals);
    }
    // add minSuffix assumptions for wires
    if (m_fWithAssump) {
      for (int i = m_GlueVars.size() - 1; i >= minLevel && i >= 0; --i)
        literals.push_back(toLit(m_GlueVars[i]));
    }
  }
  /// append assumption literals of clauses of depth [minFrame,maxFrame) in
  /// level
  /// L1 |     |
  ///----|-----|--------------minFrame=2
  /// L2 |  L2 |
  /// L3 |  L3 |  L3
  ///----|-----|------------- maxFrame=4
  /// L4 |  L4 |  L4   L4
  ///    level=1
  /// AssumpForLevel(1,2,4) = L2
  ///                         L3
  void appendAssumpForlevel(unsigned level, unsigned minFrame,
                            unsigned maxFrame, IntVector &literals) {
    AVY_ASSERT(maxFrame >= level);
    AVY_ASSERT(minFrame >= level);
    AVY_ASSERT(m_mlevelToAssumps.count(level) > 0);
    for (int i = maxFrame - 1; i >= minFrame && i >= 0; --i) {
      if (m_mlevelToAssumps[level].count(i) > 0)
        literals.push_back(m_mlevelToAssumps[level][i]);
    }
  }
  /** Find the least level amongst the lemma assumptions in core */
  unsigned findMinLevel(IntVector core) {
    unsigned minLevel = 0;
    for (int level = 0; level < m_nFrames; ++level) {
      for (auto itr : m_mlevelToAssumps[level]) {
        for (int i : core) {
          if (itr.second == i) { return level; }
        }
      }
    }
    return minLevel;
  }
  /** Find the least frame amongst the lemma assumptions in core */
  unsigned findMinFrame(IntVector core) {
    unsigned minFrame = m_nFrames - 1;
    for (int level = 0; level < m_nFrames; ++level) {
      for (auto itr : m_mlevelToAssumps[level]) {
        for (int i : core) {
          if (itr.second == i) {
            minFrame = minFrame < itr.first ? minFrame : itr.first;
          }
        }
      }
    }
    return minFrame;
  }
  /// assigns an assumption literal to each unique clause
  /// maps the clause to the highest frame in which it was seen
  lit getAssumpLit(unsigned c_id, unsigned level, unsigned frame) {
    AVY_MEASURE_FN;
    lit assumpLit;
    AVY_ASSERT(frame >= level);
    if (m_mlevelToAssumps.count(level) > 0) {
      if (m_mlevelToAssumps[level].count(frame) > 0) {
        assumpLit = m_mlevelToAssumps[level][frame];
      } else {
        assumpLit = toLit(freshVar());
        m_mlevelToAssumps[level][frame] = assumpLit;
      }
    } else {
      assumpLit = toLit(freshVar());
      m_mlevelToAssumps[level].insert(std::make_pair(frame, assumpLit));
    }
    tribool aVal = eval(assumpLit);
    AVY_ASSERT(aVal.undef());
    AVY_ASSERT(assumpLit > 0);
    return assumpLit;
  }

  void glueOutIn2(int nFrame) {
    AVY_ASSERT(m_nFrames > 1);
    AVY_ASSERT(Vec_IntSize(m_vOutputs.at(nFrame - 1)) ==
               Vec_IntSize(m_vInputs.at(nFrame)));

    lit Lit[2];

    int out, i;

    Vec_Int_t *ins = m_vInputs.at(nFrame);
    if (m_Glued[nFrame].size() == 0) {
      m_Glued[nFrame].resize(Vec_IntSize(m_vInputs.at(nFrame)), -1);
      m_vAbstractedVariables[nFrame].resize(Vec_IntSize(m_vInputs.at(nFrame)),
                                            -1);
    }
    Vec_IntForEachEntry(m_vOutputs.at(nFrame - 1), out, i) {
      lit aLit;
      tribool aVal;
      if (m_fWithAssump) {
        if (out == -1) continue; //|| glued[i] != -1
        int a;
        if (m_Glued[nFrame][i] == 1) {
          AVY_ASSERT(m_vAbstractedVariables[nFrame][i] != -1);
          a = m_vAbstractedVariables[nFrame][i];
        } else {
          a = freshVar();
          m_vAbstractedVariables[nFrame][i] = a;
        }
        aLit = toLit(a);
        aVal = eval(aLit);
        m_Glued[nFrame][i] = 1;
      }

      Lit[0] = toLit(out);
      Lit[1] = toLitCond(Vec_IntEntry(ins, i), 1);
      addGlueClause(Lit, Lit + 2, nFrame, aLit, aVal);
      Lit[0] = lit_neg(Lit[0]);
      Lit[1] = lit_neg(Lit[1]);
      addGlueClause(Lit, Lit + 2, nFrame, aLit, aVal);
    }
  }

private:
  void addGlueClause(avy::abc::lit *beg, avy::abc::lit *end, int nFrame,
                     avy::abc::lit nameLit = -1,
                     tribool aVal = tribool()) {
    if (m_fWithAssump) {
      if (aVal)
        // -- assumption set, do not add assumption to clause
        addClause(beg, end, nFrame);
      else if (!aVal)
        // -- assumption is set to false, do not add clause
        return;
      else
        // -- assumption unset, add it to clause
        addNamedClause(beg, end, nFrame, nameLit);
    } else
      addClause(beg, end, nFrame);
  }
  void markAssumpAdded(lit a) {
    if (a >= m_pEnabledAssumpLit.size()) m_pEnabledAssumpLit.resize(a + 1);
    m_pEnabledAssumpLit.set(a);
  }
};
} // namespace avy

#endif /* _UNROLLER_H_ */
