#pragma once

#include "avy/AvyAbc.h"
#include "avy/Util/AvyTribool.h"
#include "avy/Util/Stats.h"

#include "avy/abc/pdr/pdrInt.h"
#include <iostream>
#include <memory>
#include <vector>

#include "avy/Util/AvyAssert.h"

namespace avy {
using namespace avy::abc;
using namespace avy_abc_pdr;

namespace {
struct pdr_set_deleter {
  void operator()(Pdr_Set_t *p) {
    if (p) Pdr_SetDeref(p);
  }
};
} // namespace

typedef std::shared_ptr<Pdr_Set_t> PdrSetPtr;
inline PdrSetPtr pdrSetPtr(Pdr_Set_t *p) {
  if (p) Pdr_SetRef(p);
  return PdrSetPtr(p, pdr_set_deleter());
}

class Pdr {
  Aig_Man_t *m_pAig;
  Pdr_Man_t *m_pPdr;
  /// invariants
  Vec_Ptr_t *m_vInvars;
  /// last level at which the property was established
  unsigned m_nSafeLevel;

  /// conflict limit in generalization
  unsigned nGenConfLimit;

  Aig_Obj_t *cubeToAig(Pdr_Set_t *pCube, Aig_Man_t *pAig);

  int blockCube(Pdr_Set_t *pCube, bool kind = false);

  Pdr_Set_t *reduceClause(int k, Pdr_Set_t *pCube);
  int generalize(int k, Pdr_Set_t *pCube, Pdr_Set_t **ppPred,
                 Pdr_Set_t **ppCubeMin);
  void solverAddClause(int k, Pdr_Set_t *pCube);

  /**
   * based on Pdr_ManPushClauses
   *
   * \return 1 if an invariant is found, 0 if not, -1 on internal error
   */
  int pushClauses(int kMin = 1, int pkMax = 0);

  tribool tbool(int n) {
    switch (n) {
    case 1:
      return true;
    case 0:
      return false;
    case -1:
      return tribool();
    }
    AVY_UNREACHABLE();
    return false;
  }

  void Print(std::ostream &out);

public:
  Pdr(Aig_Man_t *pAig);
  ~Pdr();

  Pdr_Man_t *get() { return m_pPdr; }

  void setGenConfLimit(unsigned v) { nGenConfLimit = v; }
  unsigned getSafeLevel() { return m_nSafeLevel; }
  void setSafeLevel(unsigned v) {
    if (v > m_nSafeLevel) m_nSafeLevel = v;
  }
  void setLimit(unsigned v) { m_pPdr->pPars->nFrameMax = v; }
  void setVerbose(bool v) { m_pPdr->pPars->fVerbose = v; }
  bool isVerbose() { return m_pPdr->pPars->fVerbose != 0; }
  /** if true, load complete Cnf of the transition relation into the
      solver.  if false, only load the clauses in the cone of
      influence of the current CTI */
  void setMonoCnf(bool v) { m_pPdr->pPars->fMonoCnf = v; }
  bool isMonoCnf() { return m_pPdr->pPars->fMonoCnf != 0; }
  void setShortestPath(bool v) { m_pPdr->pPars->fShortest = v; }
  bool isShortestPath() { return m_pPdr->pPars->fShortest != 0; }

  void setSilent(bool v) { m_pPdr->pPars->fSilent = v; }

  /// -- drop all clauses from a cover
  void resetCover(unsigned level);
  void resetInvar();
  void addCoverCubes(unsigned level, Vec_Ptr_t *pCubes);
  void getCoverDeltaCubes(unsigned level, Vec_Ptr_t *pCubes);
  void getCoverCubes(unsigned level, Vec_Ptr_t *pCubes, bool withInvar = true);
  void getInvarCubes(Vec_Ptr_t *pCubes);
  void addInvarCubes(Vec_Ptr_t *pCubes);
  void addInvarCube(Pdr_Set_t *pCube);
  void addInvarToSolver(int k);

  Aig_Obj_t *getCover(unsigned level, Aig_Man_t *pAig = 0);
  Aig_Obj_t *getCoverDelta(unsigned level, Aig_Man_t *pAig = 0);

  unsigned getInvarSize() const { return Vec_PtrSize(m_vInvars); }
  unsigned getCoverDeltaSize(unsigned level) const {
    Vec_Ptr_t *vVec = Vec_VecEntry(m_pPdr->vClauses, level);
    return Vec_PtrSize(vVec);
  }
  /// count the total number of lemmas in the trace
  unsigned getNumLemmas(bool kind = false) const {
    Vec_Ptr_t *vVec;
    int i;
    unsigned size = 0;
    Pdr_Set_t *pCube;
    int j;
    Vec_VecForEachLevel(m_pPdr->vClauses, vVec, i) {
      Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) {
        size += kind ? (pCube->kind) : 1;
      }
    }
    Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j) {
      size += kind ? (pCube->kind) : 1;
    }
    return size;
  }
  /// count the total number of literals in the trace
  unsigned getNumberOfLiterals() const {
    Vec_Ptr_t *vVec;
    int i;
    unsigned size = 0;
    Pdr_Set_t *pCube;
    int j;
    Vec_VecForEachLevel(m_pPdr->vClauses, vVec, i) {
      Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) {
        size += (pCube->nLits);
      }
    }
    Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j) {
      size += (pCube->nLits);
    }
    return size;
  }

  void ensureFrames(unsigned level);
  unsigned maxFrames() { return Vec_PtrSize(m_pPdr->vSolvers); }

  void statusLn(std::ostream &out);

  /**
   * based on Pdr_ManSolveInt
   *
   * \return 1 if an invariant is found, 0 if not, -1 on internal error
   */
  int solve(bool safe = false, bool kind = false);

  /** Special version of solve used internally
   */
  int solveSafe(bool kind = false) {
    AVY_MEASURE_FN;
    return solve(true, kind);
  }
  tribool push(int kMin = 1, int kMax = 0) {
    return tbool(pushClauses(kMin, kMax));
  }

  bool validateInvariant();
  bool validateTrace(int nMax = -1);

  friend std::ostream &operator<<(std::ostream &out, Pdr &pdr);

  void markBadCube(Pdr_Set_t *pCube) { pCube->fBad = 1; }
  bool isBadCube(Pdr_Set_t *pCube) const { return pCube->fBad == 1; }

  void printCubesInfo(int nFrame);
  void findStrongerCubes();

  bool bQuipMode;
  void setQuipMode(bool on) {
    if (on)
      m_pPdr->fQuipMode = 1;
    else
      m_pPdr->fQuipMode = 0;
  }

  void getVarsScore(int nFrame, std::vector<unsigned> &score);

  unsigned getFrameAvgAge(int nFrame) const;
};

inline std::ostream &operator<<(std::ostream &out, Pdr &pdr) {
  pdr.Print(out);
  return out;
}

} // namespace avy
