#include "Pdr.h"
#include "AigPrint.h"
#include "avy/Util/AvyAssert.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"

#include "boost/format.hpp"
#include <cmath>
#include <cstdint>
#include <limits>
namespace avy_abc_pdr {
int *Pdr_ManSortByPriority(Pdr_Man_t *p, Pdr_Set_t *pCube);
} // namespace ABC_NAMESPACE

using namespace avy::abc;
using namespace avy_abc_pdr;

namespace avy {
static void eraseSubsumed(Vec_Ptr_t *vCubes, Pdr_Set_t *pCube, int start);

static void addInvarClauses(int k, void *p) {
  Pdr *pdr = static_cast<Pdr *>(p);
  pdr->addInvarToSolver(k);
}

Pdr::Pdr(Aig_Man_t *pAig) : m_pAig(pAig) {
  Pdr_Par_t *p = ABC_ALLOC(Pdr_Par_t, 1);
  Pdr_ManSetDefaultParams(p);
  m_pPdr = Pdr_ManStart(m_pAig, p, NULL);
  m_vInvars = Vec_PtrAlloc(16);
  m_nSafeLevel = 0;

  setGenConfLimit(0);
  setVerbose(false);
  setSilent(true);

  Pdr_ManSetCallbackParam(m_pPdr, this);
  Pdr_ManSetCallback(m_pPdr, addInvarClauses);
}

Pdr::~Pdr() {
  if (m_vInvars) {
    Pdr_Set_t *pCube;
    int i;
    Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, i) {
      Pdr_SetDeref(pCube);
    }
    Vec_PtrFree(m_vInvars);
  }

  if (m_pPdr) {
    Pdr_Par_t *p = m_pPdr->pPars;
    Pdr_ManStop(m_pPdr);
    ABC_FREE(p);
  }
}

void Pdr::ensureFrames(unsigned lvl) {
  AVY_MEASURE_FN;

  Pdr_Set_t *pCube;
  int j;
  for (unsigned i = Vec_PtrSize(m_pPdr->vSolvers); i <= lvl; ++i) {
    Pdr_ManCreateSolver(m_pPdr, i);
    Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j) {
      Stats::resume("ensureFrames_Invar");
      // -- load invariants into current solver
      solverAddClause(i, pCube);
      Stats::stop("ensureFrames_Invar");
    }
  }
}

void Pdr::Print(std::ostream &out) {
  out << "PDR BEGIN\n";
  out << "Frames: " << maxFrames() << "\n";

  Vec_Ptr_t *pCubes = Vec_PtrAlloc(10);
  for (unsigned i = 0; i < maxFrames(); ++i) {
    out << "F" << i << ": ";
    Vec_PtrClear(pCubes);
    getCoverDeltaCubes(i, pCubes);
    out << "size: " << Vec_PtrSize(pCubes) << "\n";
    if (m_pPdr->pPars->fVerbose)
      PrintPdrSets(out, *pCubes);
  }
  Vec_PtrFree(pCubes);

  out << "PDR END\n";
}

void Pdr::statusLn(std::ostream &out) {
  out << maxFrames() << ": ";
  Vec_Ptr_t *vVec;
  int i;
  Vec_VecForEachLevel(m_pPdr->vClauses, vVec, i) out
      << Vec_PtrSize(vVec) << (i == m_nSafeLevel ? " ! " : " ");
  out << "\n";
}

void Pdr::resetCover(unsigned level) {
  ensureFrames(level);

  Vec_Ptr_t *vVec = Vec_VecEntry(m_pPdr->vClauses, level);
  int i;
  Pdr_Set_t *pCube;

  // -- dereference all cubes we are dropping
  Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, i) Pdr_SetDeref(pCube);

  // -- drop cubes
  Vec_PtrClear(Vec_VecEntry(m_pPdr->vClauses, level));
}

void Pdr::resetInvar() {
  Pdr_Set_t *pCube;
  int i;
  Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, i) Pdr_SetDeref(pCube);
  Vec_PtrClear(m_vInvars);
}

void Pdr::addCoverCubes(unsigned level, Vec_Ptr_t *pCubes) {
  AVY_MEASURE_FN;
  ensureFrames(level);

  int j;
  Pdr_Set_t *pCube;

  LOG("pdr_verbose", logs() << "Adding cubes to level: " << level << std::endl;);

  Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) {
    LOG("pdr_verbose", logs() << j << ": " << *pCube << std::endl;);

    Vec_VecPush(m_pPdr->vClauses, level, Pdr_SetRef(pCube));
    m_pPdr->nCubes++;

    for (int i = 1; i <= (int)level; ++i)
      solverAddClause(i, pCube);
  }
}

void Pdr::getCoverDeltaCubes(unsigned level, Vec_Ptr_t *pCubes) {
  Vec_Ptr_t *vVec = Vec_VecEntry(m_pPdr->vClauses, level);
  int j;
  Pdr_Set_t *pCube;

  Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) Vec_PtrPush(pCubes, pCube);
}

void Pdr::getCoverCubes(unsigned level, Vec_Ptr_t *pCubes, bool withInvar) {
  int i;
  Vec_Ptr_t *vVec;
  int j;
  Pdr_Set_t *pCube;

  Vec_VecForEachLevelStart(m_pPdr->vClauses, vVec, i, level) {
    Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) Vec_PtrPush(pCubes, pCube);
  }

  if (withInvar)
    getInvarCubes(pCubes);
}

void Pdr::getInvarCubes(Vec_Ptr_t *pCubes) {
  Pdr_Set_t *pCube;
  int j;

  Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j)
      Vec_PtrPush(pCubes, pCube);
}

void Pdr::addInvarCubes(Vec_Ptr_t *pCubes) {
  int j;
  Pdr_Set_t *pCube;
  Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j)
      addInvarCube(Pdr_SetRef(pCube));
}

void Pdr::addInvarCube(Pdr_Set_t *pCube) {
  if (!pCube)
    return;

  eraseSubsumed(m_vInvars, pCube, 0);
  Vec_PtrPush(m_vInvars, pCube);
  for (int m = 1; m < maxFrames(); ++m)
    solverAddClause(m, pCube);
}

Aig_Obj_t *Pdr::cubeToAig(Pdr_Set_t *pCube, Aig_Man_t *pAig) {
  if (!pAig)
    pAig = m_pAig;
  Aig_Obj_t *pRes = Aig_ManConst1(pAig);

  for (int i = 0; i < pCube->nLits; ++i) {
    if (pCube->Lits[i] == -1)
      continue;

    Aig_Obj_t *pObj;

    pObj = Aig_ManCi(pAig, lit_var(pCube->Lits[i]));
    pObj = Aig_NotCond(pObj, lit_sign(pCube->Lits[i]));
    pRes = Aig_And(pAig, pRes, pObj);
  }

  return pRes;
}

Aig_Obj_t *Pdr::getCover(unsigned level, Aig_Man_t *pAig) {
  assert(level > 0);
  if (!pAig)
    pAig = m_pAig;

  Aig_Obj_t *pRes = Aig_ManConst1(pAig);
  int i;
  Vec_Ptr_t *vVec;
  Vec_VecForEachLevelStart(m_pPdr->vClauses, vVec, i, level) {
    int j;
    Pdr_Set_t *pCube;
    Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) {
      Aig_Obj_t *pAigCube = cubeToAig(pCube, pAig);
      pRes = Aig_And(pAig, pRes, Aig_Not(pAigCube));
    }
  }

  int j;
  Pdr_Set_t *pCube;
  Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j) {
    Aig_Obj_t *pAigCube = cubeToAig(pCube, pAig);
    pRes = Aig_And(pAig, pRes, Aig_Not(pAigCube));
  }
  return pRes;
}

Aig_Obj_t *Pdr::getCoverDelta(unsigned level, Aig_Man_t *pAig) {
  assert(level > 0);
  if (!pAig)
    pAig = m_pAig;

  Vec_Ptr_t *vVec = Vec_VecEntry(m_pPdr->vClauses, level);
  int j;
  Pdr_Set_t *pCube;
  Aig_Obj_t *pRes = Aig_ManConst1(pAig);

  Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) {
    Aig_Obj_t *pAigCube = cubeToAig(pCube, pAig);
    pRes = Aig_And(pAig, pRes, Aig_Not(pAigCube));
  }
  return pRes;
}

void Pdr::solverAddClause(int k, Pdr_Set_t *pCube) {
  AVY_MEASURE_FN;
//  LOG("pdr_verbose", logs() << "Adding cube to frame " << k << "\n"
//                            << *pCube << std::endl;);

  Pdr_Man_t *p = m_pPdr;
  sat_solver *pSat;
  Vec_Int_t *vLits;
  int RetValue;
  pSat = Pdr_ManSolver(p, k);
  vLits = Pdr_ManCubeToLits(p, k, pCube, 1, 0);
  RetValue = sat_solver_addclause(pSat, Vec_IntArray(vLits),
                                  Vec_IntArray(vLits) + Vec_IntSize(vLits));
  assert(RetValue == 1);
  sat_solver_compress(pSat);
}

int Pdr::generalize(int k, Pdr_Set_t *pCube, Pdr_Set_t **ppPred,
                    Pdr_Set_t **ppCubeMin) {
  AVY_MEASURE_FN;
  Pdr_Man_t *p = m_pPdr;

  Pdr_Set_t *pCubeMin, *pCubeTmp = NULL;
  int i, j, n, Lit, RetValue;
  abctime clk = Abc_Clock();
  int *pOrder;
  // if there is no induction, return
  *ppCubeMin = NULL;
  RetValue = Pdr_ManCheckCube(p, k, pCube, ppPred, p->pPars->nConfLimit);
  if (RetValue == -1)
    return -1;
  if (RetValue == 0) {
    p->tGeneral += Abc_Clock() - clk;
    return 0;
  }

  // reduce clause using assumptions
  //    pCubeMin = Pdr_SetDup( pCube );
  pCubeMin = reduceClause(k, pCube);
  if (pCubeMin == NULL)
    pCubeMin = Pdr_SetDup(pCube);

  // perform generalization
  if (!p->pPars->fSkipGeneral) {
    // sort literals by their occurences
    pOrder = Pdr_ManSortByPriority(p, pCubeMin);
    // try removing literals
    for (j = 0; j < pCubeMin->nLits; j++) {
      // use ordering
      //        i = j;
      i = pOrder[j];

      // check init state
      assert(pCubeMin->Lits[i] != -1);
      if (Pdr_SetIsInit(pCubeMin, i))
        continue;
      // try removing this literal
      Lit = pCubeMin->Lits[i];
      pCubeMin->Lits[i] = -1;
      // RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, p->pPars->nConfLimit
      // );
      RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, nGenConfLimit);
      // -- treat -1 as unsuccessful generalization
      if (RetValue == -1)
        RetValue = 0;
      if (RetValue == -1) {
        Pdr_SetDeref(pCubeMin);
        return -1;
      }
      pCubeMin->Lits[i] = Lit;
      if (RetValue == 0)
        continue;

      // remove j-th entry
      for (n = j; n < pCubeMin->nLits - 1; n++)
        pOrder[n] = pOrder[n + 1];
      j--;

      // success - update the cube
      pCubeMin = Pdr_SetCreateFrom(pCubeTmp = pCubeMin, i);
      Pdr_SetDeref(pCubeTmp);
      assert(pCubeMin->nLits > 0);
      i--;

      // get the ordering by decreasing priorit
      pOrder = Pdr_ManSortByPriority(p, pCubeMin);
    }

    if (p->pPars->fTwoRounds)
      for (j = 0; j < pCubeMin->nLits; j++) {
        // use ordering
        //        i = j;
        i = pOrder[j];

        // check init state
        assert(pCubeMin->Lits[i] != -1);
        if (Pdr_SetIsInit(pCubeMin, i))
          continue;
        // try removing this literal
        Lit = pCubeMin->Lits[i];
        pCubeMin->Lits[i] = -1;
        RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, p->pPars->nConfLimit);
        if (RetValue == -1) {
          Pdr_SetDeref(pCubeMin);
          return -1;
        }
        pCubeMin->Lits[i] = Lit;
        if (RetValue == 0)
          continue;

        // remove j-th entry
        for (n = j; n < pCubeMin->nLits - 1; n++)
          pOrder[n] = pOrder[n + 1];
        j--;

        // success - update the cube
        pCubeMin = Pdr_SetCreateFrom(pCubeTmp = pCubeMin, i);
        Pdr_SetDeref(pCubeTmp);
        assert(pCubeMin->nLits > 0);
        i--;

        // get the ordering by decreasing priorit
        pOrder = Pdr_ManSortByPriority(p, pCubeMin);
      }
  }

  assert(ppCubeMin != NULL);
  *ppCubeMin = pCubeMin;
  p->tGeneral += Abc_Clock() - clk;
  return 1;
}

Pdr_Set_t *Pdr::reduceClause(int k, Pdr_Set_t *pCube) {
  Pdr_Man_t *p = m_pPdr;

  Pdr_Set_t *pCubeMin;
  Vec_Int_t *vLits;
  int i, Entry, nCoreLits, *pCoreLits;
  // get relevant SAT literals
  nCoreLits = sat_solver_final(Pdr_ManSolver(p, k), &pCoreLits);
  // translate them into register literals and remove auxiliary
  vLits = Pdr_ManLitsToCube(p, k, pCoreLits, nCoreLits);
  // skip if there is no improvement
  if (Vec_IntSize(vLits) == pCube->nLits)
    return NULL;
  assert(Vec_IntSize(vLits) < pCube->nLits);
  // if the cube overlaps with init, add any literal
  Vec_IntForEachEntry(vLits, Entry,
                      i) if (lit_sign(Entry) == 0) // positive literal
      break;
  if (i == Vec_IntSize(vLits)) // only negative literals
  {
    // add the first positive literal
    for (i = 0; i < pCube->nLits; i++)
      if (lit_sign(pCube->Lits[i]) == 0) // positive literal
      {
        Vec_IntPush(vLits, pCube->Lits[i]);
        break;
      }
    assert(i < pCube->nLits);
  }
  // generate a starting cube
  pCubeMin =
      Pdr_SetCreateSubset(pCube, Vec_IntArray(vLits), Vec_IntSize(vLits));
  assert(!Pdr_SetIsInit(pCubeMin, -1));
  /*
  // make sure the cube works
  {
  int RetValue;
  RetValue = Pdr_ManCheckCube( p, k, pCubeMin, NULL, 0 );
  assert( RetValue );
  }
  */
  return pCubeMin;
}

static void eraseSubsumed(Vec_Ptr_t *vCubes, Pdr_Set_t *pCube, int start) {
  Pdr_Set_t *pTemp;
  int m;
  int numOfElementsRemoved = 0;
  // remove cubes in the same frame that are contained by pCubeK
  Vec_PtrForEachEntryStart(Pdr_Set_t *, vCubes, pTemp, m, start) {
    if (numOfElementsRemoved != 0) {
      Vec_PtrWriteEntry(vCubes, m - numOfElementsRemoved,
                        Vec_PtrEntry(vCubes, m));
    }
    if (!Pdr_SetContains(pTemp, pCube)) // pCube contains pTemp
      continue;
    if (pTemp->nAge > pCube->nAge)
      pCube->nAge = pTemp->nAge; // Move the age
    Pdr_SetDeref(pTemp);
    numOfElementsRemoved++;
  }
  Vec_PtrShrink(vCubes, m - numOfElementsRemoved);
}

int Pdr::pushClauses(int kMin, int pkMax) {
  AVY_MEASURE_FN;
  Pdr_Man_t *p = m_pPdr;
  Pdr_Set_t *pCubeK;
  Vec_Ptr_t *vArrayK, *vArrayK1;
  int j, k, RetValue = 0, RetValue2, kMax;
  int Counter = 0;
  abctime clk = Abc_Clock();
  Stopwatch pushTime;
  pushTime.start();

  // assert( p->iUseFrame > 0 );
  LOG("pdr_verbose", std::cerr << __FILE__ << ":" << __LINE__ << std::endl);

  {
    kMax = m_nSafeLevel;
    int nkMax = kMax + gParams.num_extra_frames;
    kMax = kMax <= nkMax ? nkMax : std::numeric_limits<std::int32_t>::max();
  }

  if (pkMax >= kMin && pkMax <= kMax)
    kMax = pkMax;

  Vec_VecForEachLevelStartStop(p->vClauses, vArrayK, k, 1, kMax) {
    if (k < kMin)
      continue;
    // -- break out if there are no more lemmas to push
    if (k > m_nSafeLevel && Vec_PtrSize(vArrayK) == 0)
      break;

    ensureFrames(k + 1);

    Vec_PtrSort(vArrayK, (int (*)(const void *, const void *))Pdr_SetCompare);
    vArrayK1 = Vec_VecEntry(p->vClauses, k + 1);
    {
      Stopwatch subTime;
      subTime.start();
      LOG("trace_size", logs() << "Number of lemmas at frame " << k
                               << " before self subsumption check "
                               << Vec_PtrSize(vArrayK) << "\n";);
      Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCubeK, j) {
        eraseSubsumed(vArrayK, pCubeK, j + 1);
      }
      LOG("trace_size",
          logs() << "Number of lemmas at frame " << k
                 << " after self subsumption check " << Vec_PtrSize(vArrayK)
                 << " Time taken "
                 << (boost::format("%.2f") % (subTime).toSeconds()) << "\n";);
    }
    Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCubeK, j) {
      Counter++;

      // remove cubes in the same frame that are contained by pCubeK
      eraseSubsumed(vArrayK, pCubeK, j + 1);

      // HG : it makes more sense to do this check before we remove subsumed
      // lemmas
      if (pCubeK->fBad == 1)
        continue;
      Stats::resume("pushClauses.Pdr_ManCheckCube");
      // check if the clause can be moved to the next frame
      RetValue2 = Pdr_ManCheckCube(p, k, pCubeK, NULL, 0);
      Stats::stop("pushClauses.Pdr_ManCheckCube");
      if (RetValue2 == -1)
        return -1;
      if (!RetValue2)
        continue;

      {
        Pdr_Set_t *pCubeMin;
        pCubeMin = reduceClause(k, pCubeK);
        if (pCubeMin != NULL) {
          //                Abc_Print( 1, "%d ", pCubeK->nLits - pCubeMin->nLits
          //                );
          Pdr_SetDeref(pCubeK);
          pCubeK = pCubeMin;
          for (int i = 1; i <= k; ++i) {
            solverAddClause(i, pCubeK);
          }
        }
      }

      // if it can be moved, add it to the next frame
      solverAddClause(k + 1, pCubeK);
      // check if the clause subsumes others
      eraseSubsumed(vArrayK1, pCubeK, 0);

      LOG("pdr_verbose", logs() << "pushed clause to level " << k+1 << " : " << *pCubeK << std::endl;);
      // add the last clause
      Vec_PtrPush(vArrayK1, pCubeK);
      Vec_PtrWriteEntry(vArrayK, j, Vec_PtrEntryLast(vArrayK));
      Vec_PtrPop(vArrayK);
      j--;
    }
    if (Vec_PtrSize(vArrayK) == 0) {
      LOG("pdr_verbose", logs() << "converged at" << k << std::endl;);
      RetValue = 1;
      break;
    }
  }

  if (RetValue != 1) {
    // clean up the last one
    vArrayK = Vec_VecEntry(p->vClauses, k);
    Vec_PtrSort(vArrayK, (int (*)(const void *, const void *))Pdr_SetCompare);
    Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCubeK, j) {
      // remove cubes in the same frame that are contained by pCubeK
      eraseSubsumed(vArrayK, pCubeK, j + 1);
    }
  } else {
    int i;
    // -- update RetValue based on safe level
    RetValue = (k <= m_nSafeLevel);

    if (!RetValue)
      RetValue = Pdr_ManCheckCube(m_pPdr, k, NULL, NULL, 100000);
    Stopwatch addTime;
    addTime.start();
    VERBOSE(3, vout() << "Pdr: Num. of invariant clauses before: " << Vec_PtrSize(m_vInvars) << "\n";);

    // -- copy frames into invariant
    Vec_VecForEachLevelStart(m_pPdr->vClauses, vArrayK, i, k + 1) {
      Vec_PtrForEachEntry(Pdr_Set_t *, vArrayK, pCubeK, j) {
        Vec_PtrPush(m_vInvars, pCubeK);
        for (int m = i + 1; m < maxFrames(); ++m)
          solverAddClause(m, pCubeK);
      }
      Vec_PtrClear(vArrayK);
    }
    VERBOSE(3, vout() << "Pdr: Num. of invariant clauses after pushing: " << Vec_PtrSize(m_vInvars) << "\n";);
    LOG("trace_size", logs() << "Time for adding Invars "
                             << (boost::format("%.2f") % (addTime).toSeconds())
                             << "\n";);
    // -- sort
    Vec_PtrSort(m_vInvars, (int (*)(const void *, const void *))Pdr_SetCompare);
    // -- remove redundant
    Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCubeK, j)
        eraseSubsumed(m_vInvars, pCubeK, j + 1);

    VERBOSE(3, vout() << "Pdr: Num. of invariant clauses after subsumption: " << Vec_PtrSize(m_vInvars) << "\n";);
    Stats::uset("Invar", Vec_PtrSize(m_vInvars));
  }

  p->tPush += Abc_Clock() - clk;
  LOG("trace_size", logs() << "Time for push "
                           << (boost::format("%.2f") % (pushTime).toSeconds())
                           << "\n";);
  return RetValue;
}

int Pdr::blockCube(Pdr_Set_t *pCube, bool kind ) {
  AVY_MEASURE_FN;
  Pdr_Man_t *p = m_pPdr;

  Pdr_Obl_t *pThis;
  Pdr_Set_t *pPred, *pCubeMin;
  int i, k, RetValue, Prio = ABC_INFINITY, Counter = 0;
  int kMax = m_nSafeLevel + 1; /* Vec_PtrSize(p->vSolvers)-1; */
  abctime clk;
  p->nBlocks++;
  LOG("pdr_verbose", logs() << "blocking cube " << *pCube << std::endl;);
  // create first proof obligation
  //    assert( p->pQueue == NULL );
  pThis = Pdr_OblStart(kMax, Prio--, pCube, NULL); // consume ref
  Pdr_QueuePush(p, pThis);
  // try to solve it recursively
  while (!Pdr_QueueIsEmpty(p)) {
    Counter++;
    pThis = Pdr_QueueHead(p);
    if (pThis->iFrame == 0)
      return 0;               // SAT
    if (pThis->iFrame > kMax) // finished this level
      return 1;
    if (p->nQueLim && p->nQueCur >= p->nQueLim) {
      p->nQueLim = p->nQueLim * 3 / 2;
      Pdr_QueueStop(p);
      return 1; // restart
    }
    pThis = Pdr_QueuePop(p);
    assert(pThis->iFrame > 0);
    assert(!Pdr_SetIsInit(pThis->pState, -1));
    p->iUseFrame = Abc_MinInt(p->iUseFrame, pThis->iFrame);

    clk = Abc_Clock();
    if (Pdr_ManCheckContainment(p, pThis->iFrame, pThis->pState)) {
      p->tContain += Abc_Clock() - clk;
      Pdr_OblDeref(pThis);
      continue;
    }
    p->tContain += Abc_Clock() - clk;

    // check if the cube is already contained
    RetValue = Pdr_ManCheckCubeCs(p, pThis->iFrame, pThis->pState);
    if (RetValue == -1) // resource limit is reached
    {
      Pdr_OblDeref(pThis);
      return -1;
    }
    if (RetValue) // cube is blocked by clauses in this frame
    {
      Pdr_OblDeref(pThis);
      continue;
    }

    // check if the cube holds with relative induction
    pCubeMin = NULL;
    RetValue = generalize(pThis->iFrame - 1, pThis->pState, &pPred, &pCubeMin);
    if (RetValue == -1) // resource limit is reached
    {
      Pdr_OblDeref(pThis);
      return -1;
    }
    if (RetValue) // cube is blocked inductively in this frame
    {
      assert(pCubeMin != NULL);

      // k is the last frame where pCubeMin holds
      k = pThis->iFrame;
      if (m_pPdr->fQuipMode)
        pCubeMin->fQuip = 1;

      // check other frames
      assert(pPred == NULL);
      for (k = pThis->iFrame; k < kMax; k++) {
        RetValue = Pdr_ManCheckCube(p, k, pCubeMin, NULL, 0);
        if (RetValue == -1) {
          Pdr_OblDeref(pThis);
          return -1;
        }
        if (!RetValue)
          break;
      }

      // add new clause
      if (p->pPars->fVeryVerbose) {
        Abc_Print(1, "Adding cube ");
        Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
        Abc_Print(1, " to frame %d.\n", k);
      }
      // set priority flops
      for (i = 0; i < pCubeMin->nLits; i++) {
        assert(pCubeMin->Lits[i] >= 0);
        assert((pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
        Vec_IntAddToEntry(p->vPrio, pCubeMin->Lits[i] / 2, 1);
      }

      pCubeMin->kind=kind;
      Vec_VecPush(p->vClauses, k, pCubeMin); // consume ref
      p->nCubes++;
      // add clause
      LOG("pdr_verbose", logs() << "mkSafe insert clause "<< k << " " << *pCubeMin << std::endl;);
      for (i = 1; i <= k; i++)
        solverAddClause(i, pCubeMin);
      // schedule proof obligation
      if (!p->pPars->fShortest) {
        pThis->iFrame = k + 1;
        pThis->prio = Prio--;
        Pdr_QueuePush(p, pThis);
      } else {
        Pdr_OblDeref(pThis);
      }
    } else {
      assert(pCubeMin == NULL);
      assert(pPred != NULL);
      pThis->prio = Prio--;
      Pdr_QueuePush(p, pThis);

      pThis = Pdr_OblStart(pThis->iFrame - 1, Prio--, pPred, Pdr_OblRef(pThis));
      Pdr_QueuePush(p, pThis);
    }

    // check termination
    if (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->RunId))
      return -1;
    if (p->timeToStop && Abc_Clock() > p->timeToStop)
      return -1;
    if (p->timeToStopOne && Abc_Clock() > p->timeToStopOne)
      return -1;
    if (p->pPars->nTimeOutGap && p->pPars->timeLastSolved &&
        Abc_Clock() >
            p->pPars->timeLastSolved + p->pPars->nTimeOutGap * CLOCKS_PER_SEC)
      return -1;
  }
  return 1;
}

/**
 * Main solve loop.
 */
int Pdr::solve(bool safe, bool kind) {
  ScoppedStats __stats__("Pdr_solve");
  Pdr_Man_t *p = m_pPdr;

  int fPrintClauses = 0;
  Pdr_Set_t *pCube = NULL;
  int k, RetValue = -1;
  abctime clkStart = Abc_Clock(), clkOne = 0;
  p->timeToStop = p->pPars->nTimeOut
                      ? p->pPars->nTimeOut * CLOCKS_PER_SEC + Abc_Clock()
                      : 0;
  // assert( Vec_PtrSize(p->vSolvers) == 0 );
  // create the first timeframe
  p->pPars->timeLastSolved = Abc_Clock();
  ensureFrames(k = 0);

  p->iOutCur = 0;

  while (1) {
    LOG("pdr_verbose", logs() << "At loop iteration " << k << std::endl;);

    p->nFrames = k;
    // assert( k == Vec_PtrSize(p->vSolvers)-1 );
    p->iUseFrame = ABC_INFINITY;
    Aig_Obj_t *pObj = Aig_ManCo(p->pAig, p->iOutCur);
    // check if the output is trivially solved
    if (Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig)) {
      continue;
    }
    // check if the output is trivially solved
    if (Aig_ObjChild0(pObj) == Aig_ManConst1(p->pAig)) {
      AVY_ASSERT(!safe);
    }
    // try to solve this output
    if (p->pTime4Outs) {
      assert(p->pTime4Outs[p->iOutCur] > 0);
      clkOne = Abc_Clock();
      p->timeToStopOne = p->pTime4Outs[p->iOutCur] + Abc_Clock();
    }
    while (1) {
      //fast forward to last frame if the trace is known to be safe
      if(safe && k<(m_pPdr->pPars->nFrameMax-1))
        break;
      RetValue = Pdr_ManCheckCube(p, k, NULL, &pCube, p->pPars->nConfLimit);
      if (RetValue == 1)
        break;
      if (RetValue == -1) {
        AVY_ASSERT(!safe);
        p->pPars->iFrame = k;
        return -1;
      }
      if (RetValue == 0) {
        RetValue = blockCube(pCube,kind);
        if (RetValue == -1) {
          AVY_ASSERT(!safe);
          p->pPars->iFrame = k;
          p->pAig->pSeqModel = Pdr_ManDeriveCex(p);
          return -1;
        }
        if (RetValue == 0) {
          if (!safe) {
            p->pPars->iFrame = k;
            p->pAig->pSeqModel = Pdr_ManDeriveCex(p);
            return 0;
          }
          AVY_ASSERT(!safe);
        }
        if (p->pPars->fVerbose)
          Pdr_ManPrintProgress(p, 0, Abc_Clock() - clkStart);
      }
    }
    if (p->pTime4Outs) {
      abctime timeSince = Abc_Clock() - clkOne;
      assert(p->pTime4Outs[p->iOutCur] > 0);
      p->pTime4Outs[p->iOutCur] = (p->pTime4Outs[p->iOutCur] > timeSince)
                                      ? p->pTime4Outs[p->iOutCur] - timeSince
                                      : 0;
      if (p->pTime4Outs[p->iOutCur] == 0 &&
          (p->vCexes == NULL || Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL)) {
        p->pPars->nDropOuts++;
        if (p->pPars->vOutMap)
          Vec_IntWriteEntry(p->pPars->vOutMap, p->iOutCur, -1);
        //                    printf( "Dropping output %d.\n", p->iOutCur );
      }
      p->timeToStopOne = 0;
    }

    if (p->pPars->fVerbose)
      Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
    // open a new timeframe
    p->nQueLim = p->pPars->nRestLimit;
    assert(pCube == NULL);
    Pdr_ManSetPropertyOutput(p, k);
    m_nSafeLevel = k;
    ensureFrames(++k);
    if (fPrintClauses) {
      Abc_Print(1, "*** Clauses after frame %d:\n", k);
      Pdr_ManPrintClauses(p, 0);
    }

    if (safe)
      RetValue = 0;
    else
      // push clauses into this timeframe
      RetValue = pushClauses();

    if (RetValue == -1) {
      if (p->pPars->fVerbose)
        Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
      if (!p->pPars->fSilent) {
        if (p->timeToStop && Abc_Clock() > p->timeToStop)
          Abc_Print(1, "Reached timeout (%d seconds).\n", p->pPars->nTimeOut);
        else
          Abc_Print(1, "Reached conflict limit (%d).\n", p->pPars->nConfLimit);
      }
      p->pPars->iFrame = k;
      return -1;
    }
    if (RetValue) {
      if (p->pPars->fVerbose)
        Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
      if (!p->pPars->fSilent)
        Pdr_ManReportInvariant(p);
      if (!p->pPars->fSilent)
        Pdr_ManVerifyInvariant(p);
      p->pPars->iFrame = k;
      // count the number of UNSAT outputs
      p->pPars->nProveOuts =
          Saig_ManPoNum(p->pAig) - p->pPars->nFailOuts - p->pPars->nDropOuts;
      // convert previously 'unknown' into 'unsat'
      if (p->pPars->vOutMap)
        for (k = 0; k < Saig_ManPoNum(p->pAig); k++)
          if (Vec_IntEntry(p->pPars->vOutMap, k) == -2) // unknown
            Vec_IntWriteEntry(p->pPars->vOutMap, k, 1); // unsat
      return p->vCexes ? 0 : 1;                         // UNSAT
    }
    if (p->pPars->fVerbose)
      Pdr_ManPrintProgress(p, 0, Abc_Clock() - clkStart);

    // check termination
    if (p->pPars->nFrameMax && k >= p->pPars->nFrameMax) {
      if (p->pPars->fVerbose)
        Pdr_ManPrintProgress(p, 1, Abc_Clock() - clkStart);
      if (!p->pPars->fSilent)
        Abc_Print(1, "Reached limit on the number of timeframes (%d).\n",
                  p->pPars->nFrameMax);
      p->pPars->iFrame = k;

      return -1;
    }
  }
  AVY_ASSERT(!safe);
  return -1;
}

/// Adapted from Pdr_ManVerifyInvariant
bool Pdr::validateInvariant() {
  bool res = true;

  Pdr_Man_t *p = m_pPdr;
  sat_solver *pSat;
  Vec_Int_t *vLits;
  Vec_Ptr_t *vCubes;
  Pdr_Set_t *pCube;
  int i, kThis, RetValue, Counter = 0;

  // collect cubes used in the inductive invariant
  vCubes = m_vInvars;
  // create solver with the cubes
  kThis = Vec_PtrSize(p->vSolvers);
  pSat = Pdr_ManCreateSolver(p, kThis);

  Stats::uset("Invar", Vec_PtrSize(vCubes));

  // add the clauses
  Vec_PtrForEachEntry(Pdr_Set_t *, vCubes, pCube, i) {
    vLits = Pdr_ManCubeToLits(p, kThis, pCube, 1, 0);
    RetValue = sat_solver_addclause(pSat, Vec_IntArray(vLits),
                                    Vec_IntArray(vLits) + Vec_IntSize(vLits));
    AVY_ASSERT(RetValue);
    sat_solver_compress(pSat);
  }
  // check each clause
  Vec_PtrForEachEntry(Pdr_Set_t *, vCubes, pCube, i) {
    vLits = Pdr_ManCubeToLits(p, kThis, pCube, 0, 1);
    RetValue =
        sat_solver_solve(pSat, Vec_IntArray(vLits),
                         Vec_IntArray(vLits) + Vec_IntSize(vLits), 0, 0, 0, 0);
    if (RetValue != l_False) {
      VERBOSE(2, vout() << "Warning: "
                        << "Verification of clause " << *pCube << " failed.\n";);
      Counter++;
      res = false;
    }
  }
  int nPropHolds = Pdr_ManCheckCube(p, kThis, NULL, NULL, 100000);
  if (nPropHolds != 1) {
    VERBOSE(2, vout() << "Verification failed. Invariant is not SAFE\n";);
    res = false;
  } else if (Counter)
    VERBOSE(2, vout() << "Warning: "
                      << "Verification of " << Counter
                      << " clauses has failed.\n";);
  else
    VERBOSE(2, vout() << "Verification of invariant with "
                      << Vec_PtrSize(vCubes) << " clauses was successful.";);

  // -- in debug mode, fail with assertion
  AVY_ASSERT(res && "PDR: Validation of Invariant Failed");

  // -- delete pdr object to avoid accidental use
  Pdr_Par_t *pars = m_pPdr->pPars;
  Pdr_ManStop(m_pPdr);
  ABC_FREE(pars);
  m_pPdr = NULL;

  return res;
}

bool Pdr::validateTrace(int nMax) {
  bool res = true;
  unsigned max = m_nSafeLevel + 1; // maxFrames () - 1;
  unsigned count = 0;

  if (nMax >= 0 && ((unsigned int)nMax) <= maxFrames())
    max = nMax;
  m_pPdr->iOutCur = 0;
  for (unsigned i = 0; i < max; ++i) {
    if (Pdr_ManCheckCube(m_pPdr, i, NULL, NULL, 100000) != 1) {
      count++;
      VERBOSE(2, vout() << "Frame " << i << " is NOT safe\n");
      res = false;
    }
  }
  return res;
}

void Pdr::printCubesInfo(int nFrame) {
  Vec_Ptr_t *vVec =
      (nFrame >= 0) ? Vec_VecEntry(m_pPdr->vClauses, nFrame) : m_vInvars;
  int j;
  Pdr_Set_t *pCube;

  VERBOSE(4, vout() << "Printing cubes' infor for frame: " << nFrame << "\n";
          Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) vout()
          << "AGE: " << pCube->nAge << " DEPTH: " << pCube->nDepth
          << " Orig Frame: " << pCube->nOrigF << " From Quip: " << pCube->fQuip
          << " Generated Conflicts: " << pCube->nConfl
          << " Generated Invars: " << pCube->nInvar << "\n");
}

void Pdr::findStrongerCubes() {
  int j;
  Pdr_Set_t *pCube;

  unsigned counter = 0;
  for (int f = 0; f < Vec_VecSize(m_pPdr->vClauses); f++) {
    Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j) {
      Vec_Ptr_t *vVec = Vec_VecEntry(m_pPdr->vClauses, f);

      int i;
      Pdr_Set_t *pCubeF;
      Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCubeF, i) {
        if (Pdr_SetContains(pCube, pCubeF)) {
          counter++;
          VERBOSE(4, vout() << "Found a stronger cube:\n"
                            << "\t Orig: ID=" << pCube->Sign << " size="
                            << pCube->nLits << " origF=" << pCube->nOrigF
                            << "\n\t Strong: ID=" << pCubeF->Sign
                            << " size=" << pCubeF->nLits
                            << " origF=" << pCubeF->nOrigF << "\n");
        }
      }
    }
  }

  VERBOSE(4, vout() << "OVERALL - found " << counter
                    << " stronger clauses out of " << Vec_PtrSize(m_vInvars)
                    << " invar clauses\n");
}

void Pdr::addInvarToSolver(int k) {
  Pdr_Set_t *pCube;
  int j;

  Vec_PtrForEachEntry(Pdr_Set_t *, m_vInvars, pCube, j)
      solverAddClause(k, pCube);
}

void Pdr::getVarsScore(int nFrame, std::vector<unsigned> &score) {
  Vec_Ptr_t *vVec = Vec_VecEntry(m_pPdr->vClauses, nFrame);
  int j;
  Pdr_Set_t *pCube;

  Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) {
    for (int i = 0; i < pCube->nLits; i++) {
      int var = lit_var(pCube->Lits[i]);
      score[var] += 1;
    }
  }
}

unsigned Pdr::getFrameAvgAge(int nFrame) const {
  Vec_Ptr_t *vVec = NULL;
  if (nFrame == -1)
    vVec = m_vInvars;
  else
    vVec = Vec_VecEntry(m_pPdr->vClauses, nFrame);
  unsigned nSize = Vec_PtrSize(vVec);
  if (nSize == 0)
    return 0;
  int j;
  Pdr_Set_t *pCube;
  unsigned nSum = 0;
  Vec_PtrForEachEntry(Pdr_Set_t *, vVec, pCube, j) { nSum += pCube->nAge; }

  return (floor((nSum / nSize) + 0.5));
}

} // namespace avy
