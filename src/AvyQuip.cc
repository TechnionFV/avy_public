#include "AvyQuip.h"
using namespace avy::abc;
using namespace avy_abc_pdr;

static int lemmaCompare(Pdr_Set_t **pp1, Pdr_Set_t **pp2);
static Aig_Obj_t *cubeToAig(Pdr_Set_t *pCube, Aig_Man_t *pAig);



namespace avy {
template <typename Sat>
tribool AvyQuip::operator()(unsigned nFrame, Sat &solver, Muser2 &muser,
                            Unroller<Sat> &unroller,
                            UnsatCoreComputer<Sat> &unsatCoreComputer) {
  AVY_MEASURE_FN;
  tribool RetValue = false;

  Pdr *pPdr = m.getPdr();
  AigManPtr TheAig = m.getAig();

  Aig_Man_t *pSkeleton = Aig_ManStart((&*TheAig)->nRegs);
  for (int i = 0; i < (&*TheAig)->nRegs; i++) Aig_ObjCreateCi(pSkeleton);

  Vec_Ptr_t *pCubesNew = Vec_PtrAlloc(16);
  Pdr_Set_t *pNewCube;

  solver.setBudget(1.1 * solver.getNumOfConflicts());
  Vec_Ptr_t *pCubes = Vec_PtrAlloc(16);
  pPdr->getCoverDeltaCubes(nFrame, pCubes);
  unsigned total = pPdr->getCoverDeltaSize(nFrame);
  if (total == 0) return false;
  total = (total < 100)
              ? floor((double)total * 0.9 + 0.5)
              : floor((double)total * 0.5 +
                      0.5); //(total <= 5) ? total : (double)total * 0.4;
  bool pushed = true;

  for (int itr = 0; itr < total && pushed; itr++) {
    pushed = false;
    Vec_PtrSort(pCubes, (int (*)(const void *, const void *))lemmaCompare);
    Pdr_Set_t *pCube;
    int j;
    std::vector<AigManPtr> aigs;
    std::vector<PdrSetPtr> cubes;

    Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) {
      if (pCube->nAge >= 10) pCube->fBad = 1;
      if (pCube->fBad || pCube->nRefs == 2) continue;
      // -- set Depth to at least 1 for all cubes that are already here
      if (pCube->nDepth == 0) pCube->nDepth = 1;
      AigManPtr pAig = aigPtr(Aig_ManStartFrom(pSkeleton));
      Aig_Obj_t *p = cubeToAig(pCube, &*pAig);
      Aig_ObjCreateCo(&*pAig, p);
      aigs.push_back(pAig);
      cubes.push_back(pdrSetPtr(pCube));
    }
    // Vec_PtrFree (pCubes);
    // pCubes = NULL;

    unsigned countBad = 0;
    VERBOSE(1, vout() << "Quip START: " << total << " lemmas\n");
    for (unsigned i = 0; i < aigs.size() && itr < total; i++) {
      pCube = cubes[i].get();

      // -- if pCube the reference count is not 2, pCube was deleted
      // -- (because it was subsumed). We might still want to push it though.
      if (pCube->nRefs != 2) {
        // -- nothing to do, it will be deleted when cubes moves out of scope
        // itr++;
        continue;
      }
      // -- if this is not the first iteration
      else if (i > 0) {
        Vec_PtrClear(pCubesNew);
        // -- get the new frame after pushing
        pPdr->getCoverDeltaCubes(nFrame, pCubesNew);
        bool found = false;
        // -- find the current cube in the new set
        Vec_PtrForEachEntry(Pdr_Set_t *, pCubesNew, pNewCube, j) {
          if (pNewCube == pCube) {
            found = true;
            break;
          }
        }
        Vec_PtrClear(pCubesNew);
        // -- if pCube is no longer in the frame. It must have been
        // -- pushed forward. (If it was deleted for another reason,
        // -- its reference count would have been <2).
        if (!found) {
          // HG : do we unintentionally skip the next cube as well ?
          itr++;
          pCube->nAge++;
          continue;
        }
      }

      // -- construct the appropriate circuit
      AigManPtr pAig = aigs[i];
      AigManPtr newTr =
          aigPtr(Aig_ManReplacePo(&*m.getVc()->getActual(), &*pAig, false));
      newTr = aigPtr(Aig_ManGiaDup(&*newTr));
      Aig_Man_t *pTemp = (Aig_ManDupSinglePo(&*newTr, 0, false));
      Aig_ManRebuild(&pTemp);
      AigManPtr pBad = aigPtr(pTemp);

      VERBOSE(3,
              vout() << "Trying to push a lemma with depth: " << pCube->nDepth
                     << " and age: " << pCube->nAge << std::endl);
      unsigned nOldConfl = solver.getNumOfConflicts();
      // -- run bmc to check whether current cube is reachable
      tribool res =
          m.doBmc(nFrame, solver, muser, unroller, pBad, &unsatCoreComputer);

      if (res) {
        // -- the cube is reachable. Mark it fBad.
        extractReachableState<Sat>(solver, unroller);
        VERBOSE(1, vout() << "Bad lemma " << itr << std::endl;);
        pCube->fBad = 1;
        Stats::count("BadLemmas");
        AVY_ASSERT(pCube->nRefs >= 2);
        if (countBad == 40 /*(0.2 * total)*/) break;
        countBad++;
      } else if (!res) {
        VERBOSE(1, vout() << "Pushed lemma " << itr << std::endl;);
        pushed = true;
        pCube->nAge++;
        pCube->nConfl = solver.getNumOfConflicts() - nOldConfl;
        // -- lemmas pushed by quip
        Stats::count("QuipLemmas");
        // -- if there is no core, the proof is trivial, no support needed.
        if (m.getLastCoreSize() <= 1) {
          itr++;
          continue;
        }

        AigManPtr itp = aigPtr(solver.getInterpolant(unroller.getBadLit(),
                                                     unroller.getAllOutputs(),
                                                     Saig_ManRegNum(&*TheAig)));

        Stats::uset("OrigItp", Aig_ManAndNum(&*itp));
        // -- simplify
        if (gParams.itp_simplify) {
          itp = aigPtr(Aig_ManSimplifyComb(&*itp));
          Stats::uset("SimpItp", Aig_ManAndNum(&*itp));
          VERBOSE(2, Aig_ManPrintStats(&*itp));
        }

        VERBOSE(3, Stats::PrintBrunch(vout()););

        if (gParams.opt_bmc) {
          std::vector<IntVector> equivs = m.getVc()->getFrameEquivs();
          m.findItpConstraints(itp, equivs, pBad);
        }

        unsigned nOldInvars = pPdr->getInvarSize();
        if (m.doPdrTrace(itp, true)) {
          outs() << "0\nb0\n.\n";
          VERBOSE(1, pPdr->statusLn(vout()););
          Stats::set("Result", "UNSAT");
          RetValue = true;
          pushed = false;
          pCube->nInvar = pPdr->getInvarSize() - nOldInvars;
          m.printInvCert(gParams.certificate);
          break;
        }
        pCube->nInvar = pPdr->getInvarSize() - nOldInvars;

        for (int f = 1; f <= nFrame; f++) {
          pPdr->getCoverDeltaCubes(f, pCubesNew);
          Vec_PtrForEachEntry(Pdr_Set_t *, pCubesNew, pNewCube,
                              j) if (pNewCube->nDepth == 0) pNewCube->nDepth =
              pCube->nDepth + (nFrame - f) + 1;
          Vec_PtrClear(pCubesNew);
        }

        pPdr->getCoverCubes(nFrame + 1, pCubesNew, true);
        Pdr_Set_t *pTemp;
        unsigned pdrPushed = 0;
        Vec_PtrForEachEntryStart(Pdr_Set_t *, pCubesNew, pTemp, j, 0) {
          if (Pdr_SetContains(pTemp, pCube)) {
            VERBOSE(2, vout() << "Found it... updating age\n";);
            pTemp->nAge = pCube->nAge;
            pTemp->nConfl = pCube->nConfl;
            pTemp->nInvar = pCube->nInvar;
            continue;
          }
          // Now look to find how many lemmas were pdr-pushed due to quip
          for (unsigned x = 0; x < cubes.size(); x++) {
            if (Pdr_SetContains(pTemp, cubes[x].get())) pdrPushed++;
          }
        }
        Vec_PtrClear(pCubesNew);
        VERBOSE(2, vout() << "\t" << pdrPushed
                          << " lemmas were pdr-pushed due to quip...\n";);

        Vec_PtrClear(pCubes);
        pPdr->getCoverDeltaCubes(nFrame, pCubes);

        m.doStrengthenVC();
        break;
      } else {
        VERBOSE(1, vout() << "Failed to decide lemma " << i << std::endl;);
        break;
      }
    }
  }
  VERBOSE(1, vout() << "Quip END:" << total << " lemmas\n";);
  Vec_PtrFree(pCubesNew);
  Vec_PtrFree(pCubes);

  solver.setBudget(-1);
  return RetValue;
  }

  template <typename Sat>
  void AvyQuip::extractReachableState(Sat &s, Unroller<Sat> &unroller) {
    // Allocate a new reachable state in the vector and get it
    m_ReachableStates.resize(m_ReachableStates.size() + 1);
    boost::dynamic_bitset<> &reach = m_ReachableStates.back();
    int nRegs = Aig_ManRegNum(&*m.getAig());
    // TODO: stick_error adds an extra latch - handle that.
    if (gParams.stick_error) {
      assert(false);
      std::exit(-1);
    }

    // Assign the number of bits for the state
    reach.resize(nRegs);

    abc::Vec_Int_t *regs = unroller.getOutputs(unroller.frames() - 2);

    // Set the value
    int reg, j;
    Vec_IntForEachEntry(regs, reg, j) { reach[j] = s.getVarVal(reg); }
  }
}

// =======================================================================
// Utility methods. Only used in this translation unit
// =======================================================================

static Aig_Obj_t *cubeToAig(Pdr_Set_t *pCube, Aig_Man_t *pAig) {
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

static int lemmaCompare(Pdr_Set_t **pp1, Pdr_Set_t **pp2) {
  Pdr_Set_t *p1 = *pp1;
  Pdr_Set_t *p2 = *pp2;
#if 1
  if (p1->fQuip < p2->fQuip)
    return -1;
  else if (p1->fQuip == p2->fQuip) {
    if (p1->nAge < p2->nAge)
      return -1;
    else if (p1->nAge == p2->nAge) {
      if (p1->nDepth < p2->nDepth)
        return -1;
      else if (p1->nDepth == p2->nDepth) {
        if (p1->nLits < p2->nLits)
          return -1;
        else if (p1->nLits == p2->nLits) {
          if (p1->nOrigF > p2->nOrigF)
            return -1;
          else if (p1->nOrigF == p2->nOrigF) {
            if (p1->nInvar > p2->nInvar)
              return -1;
          }
        }
      }
    }
  }
#else
  if (p1->fQuip < p2->fQuip)
    return -1;
  else if (p1->fQuip == p2->fQuip)
    if (p1->nDepth < p2->nDepth)
      return -1;
    else if (p1->nDepth == p2->nDepth)
      if (p1->nAge < p2->nAge)
        return -1;
      else if (p1->nAge == p2->nAge)
        if (p1->nOrigF > p2->nOrigF)
          return -1;
        else if (p1->nOrigF == p2->nOrigF)
          if (p1->nLits < p2->nLits)
            return -1;
          else if (p1->nLits == p2->nLits)
            if (p1->nInvar > p2->nInvar)
              return -1;
            else if (p1->nInvar == p2->nInvar)
              if (p1->nConfl < p2->nConfl)
                return -1;
#endif
  return 1;
}

// Explicit template instances. Extend as needed.
template avy::tribool avy::AvyQuip::
operator()<avy::ItpMinisat>(unsigned, avy::ItpMinisat &, Muser2 &muser,
                            Unroller<avy::ItpMinisat> &,
                            UnsatCoreComputer<avy::ItpMinisat> &);
template avy::tribool avy::AvyQuip::
operator()<avy::ItpGlucose>(unsigned, avy::ItpGlucose &, Muser2 &muser,
                            Unroller<avy::ItpGlucose> &,
                            UnsatCoreComputer<avy::ItpGlucose> &);
template avy::tribool avy::AvyQuip::
operator()<avy::ItpCadical>(unsigned, avy::ItpCadical &, Muser2 &muser,
                            Unroller<avy::ItpCadical> &,
                            UnsatCoreComputer<avy::ItpCadical> &);