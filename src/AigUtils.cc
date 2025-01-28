#include "aig/gia/giaAig.h"
#include "aig/saig/saig.h"
#include "proof/cec/cec.h"
#include "proof/dch/dch.h"

#include "AigUtils.h"
#include "avy/Util/AvyAssert.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"

namespace ABC_NAMESPACE {
Aig_Obj_t *Aig_Mux2(Aig_Man_t *p, Aig_Obj_t *pC, Aig_Obj_t *p1, Aig_Obj_t *p0);
// extern Gia_Man_t * Gia_SweeperSweep( Gia_Man_t * p, Vec_Int_t * vProbeOuts,
// int nWords, int nConfs, int fVerify, int fVerbose );
extern Gia_Man_t *Gia_SweeperSweep(Gia_Man_t *p, Vec_Int_t *vProbeOuts,
                                   int nWords, int nConfs, int fVerbose);
} // namespace ABC_NAMESPACE

using namespace avy::abc;
namespace avy {

/**
 * Duplicate p but keep only one specified output , or none if nPo is -1
 */
Aig_Man_t *Aig_ManDupSinglePo(Aig_Man_t *p, int nPo, bool fKeepRegs) {
  AVY_ASSERT(fKeepRegs == false || Aig_ManRegNum(p) > 0);
  AVY_ASSERT(nPo < 0 || Aig_ManCoNum(p) >= nPo);

  // create the new manager
  Aig_Man_t *pNew = Aig_ManStart(Aig_ManObjNumMax(p));
  pNew->pName = Abc_UtilStrsav(p->pName);
  pNew->pSpec = Abc_UtilStrsav(p->pSpec);
  pNew->nTruePis = p->nTruePis;
  if (nPo < 0)
    pNew->nTruePos = Saig_ManConstrNum(p);
  else
    pNew->nTruePos = Saig_ManConstrNum(p) + 1;
  if (fKeepRegs)
    pNew->nRegs = p->nRegs;
  else
    pNew->nRegs = 0;

  // -- move nodes
  Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);

  // -- inputs
  int i;
  Aig_Obj_t *pObj;
  Aig_ManForEachCi(p, pObj, i) {
    pObj->pData = Aig_ObjCreateCi(pNew);
  }

  // duplicate internal nodes
  Aig_ManForEachNode(p, pObj, i) {
    pObj->pData =
      Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
  }

  // create constraint outputs
  Saig_ManForEachPo(p, pObj, i) {
    if (i < Saig_ManPoNum(p) - Saig_ManConstrNum(p))
      continue;
    Aig_ObjCreateCo(pNew, Aig_Not(Aig_ObjChild0Copy(pObj)));
  }

  if (fKeepRegs) {
    // -- registers
    Saig_ManForEachLi(p, pObj, i)
        Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));
  }

  if (nPo >= 0) {
    AVY_ASSERT(Aig_ObjChild0Copy(Aig_ManCo(p, nPo)) != NULL);
    Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(Aig_ManCo(p, nPo)));
  }

  Aig_ManCleanData(p);
  Aig_ManCleanup(pNew);

  return pNew;
}

/**
    Replace or create PO of pSeqMan using pCombMan.
    CI of pCombMan are mapped to Registers of pSeqMan.
 */
Aig_Man_t *Aig_ManReplacePo(Aig_Man_t *pSeqMan, Aig_Man_t *pCombMan,
                            bool fCompl = false) {
  // Only one property output.
  AVY_ASSERT(Saig_ManPoNum(pSeqMan) - Saig_ManConstrNum(pSeqMan) == 1 &&
             "pSeqMan has more than one property output");

  AVY_ASSERT(Aig_ManRegNum(pSeqMan) > 0 && "pSeqMan is not sequential");
  AVY_ASSERT(Aig_ManRegNum(pCombMan) == 0);
  AVY_ASSERT(Aig_ManCoNum(pCombMan) == 1);
  AVY_ASSERT(Aig_ManCiNum(pCombMan) == Saig_ManRegNum(pSeqMan));
  AVY_ASSERT(Saig_ManConstrNum(pSeqMan) == 0);

  Aig_ManCleanData(pSeqMan);
  Aig_ManCleanData(pCombMan);

  // create the new manager
  Aig_Man_t *pNew =
      Aig_ManStart(Aig_ManObjNumMax(pSeqMan) + Aig_ManObjNumMax(pCombMan));
  pNew->pName = Abc_UtilStrsav(pSeqMan->pName);
  pNew->pSpec = Abc_UtilStrsav(pSeqMan->pSpec);

  // -- move pSeqMan
  Aig_ManConst1(pSeqMan)->pData = Aig_ManConst1(pNew);

  // -- inputs
  int i;
  Aig_Obj_t *pObj;
  Aig_ManForEachCi(pSeqMan, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);

  // set registers
  pNew->nTruePis = pSeqMan->nTruePis;
  pNew->nTruePos = Saig_ManConstrNum(pSeqMan) + 1;
  pNew->nRegs = pSeqMan->nRegs;

  // duplicate internal nodes
  Aig_ManForEachNode(pSeqMan, pObj, i) {
    pObj->pData =
      Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
  }

  // -- move pCombMan
  Aig_ManConst1(pCombMan)->pData = Aig_ManConst1(pNew);
  Saig_ManForEachLo(pSeqMan, pObj, i) {
    AVY_ASSERT(Aig_ManCiNum(pCombMan) > i); // XXX factor outside the loop?
    // -- map CI in the Miter to where Lo of pSeqMan is mapped in pNew
    Aig_ManCi(pCombMan, i)->pData = pObj->pData;
  }

  // -- sanity check. No missing CI
  Aig_ManForEachCi(pCombMan, pObj, i) AVY_ASSERT(pObj->pData != NULL);

  // -- copy nodes
  Aig_ManForEachNode(pCombMan, pObj, i) {
    pObj->pData =
        Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));
    AVY_ASSERT(pObj->pData != NULL);
  }

  // -- po
  AVY_ASSERT(Aig_ObjChild0Copy(Aig_ManCo(pCombMan, 0)) != NULL);
  Aig_ObjCreateCo(
      pNew, Aig_NotCond(Aig_ObjChild0Copy(Aig_ManCo(pCombMan, 0)), fCompl));

  // -- wire circuit latches
  Saig_ManForEachLi(pSeqMan, pObj, i)
      Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));

  Aig_ManCleanData(pSeqMan);
  Aig_ManCleanData(pCombMan);

  Aig_ManCleanup(pNew);
  return pNew;
}

/** Duplicate pAig by converting to Gia and back */
Aig_Man_t *Aig_ManGiaDup(Aig_Man_t *pAig) {
  Gia_Man_t *pGia = Gia_ManFromAigSimple(pAig);
  Aig_Man_t *pNewAig = Gia_ManToAigSimple(pGia);
  Gia_ManStop(pGia);
  pNewAig->nTruePis = pAig->nTruePis;
  pNewAig->nTruePos = pAig->nTruePos;
  return pNewAig;
}

/** Rebuild an Aig in-pace by converting to Gia and back*/
Aig_Man_t *Aig_ManRebuild(Aig_Man_t **ppAig) {
  Aig_Man_t *pRes = Aig_ManGiaDup(*ppAig);
  Aig_ManStop(*ppAig);
  *ppAig = pRes;
  return pRes;
}

/** Rebuild an Aig */
void Aig_ManRebuild(Aig_Man_t *pAig, AigManPtr &res) {
  Aig_Man_t *pRes = Aig_ManGiaDup(pAig);
  res = aigPtr(pRes);
}

/** Debug code: compare two aig objects and print if they are different */
bool Aig_ObjDbgCompare(Aig_Obj_t *pObj1, Aig_Obj_t *pObj2) {
  AVY_ASSERT(Aig_IsComplement(pObj1) == Aig_IsComplement(pObj2));
  pObj1 = Aig_Regular(pObj1);
  pObj2 = Aig_Regular(pObj2);
  if (Aig_ObjId(pObj1) != Aig_ObjId(pObj2)) {
    errs() << "Left: " << Aig_ObjId(pObj1)
           << " | Right: " << Aig_ObjId(pObj2) << "\n";
    AVY_UNREACHABLE();
  }

  return true;
}

/** Debug code: compare two aigs and print if they are different */
bool Aig_ManDbgCompare(Aig_Man_t *pAig1, Aig_Man_t *pAig2) {
  AVY_ASSERT(Aig_ManCiNum(pAig1) == Aig_ManCiNum(pAig2));
  AVY_ASSERT(Aig_ManCoNum(pAig1) == Aig_ManCoNum(pAig2));
  AVY_ASSERT(Aig_ManBufNum(pAig1) == Aig_ManBufNum(pAig2));
  AVY_ASSERT(Aig_ManAndNum(pAig1) == Aig_ManAndNum(pAig2));
  AVY_ASSERT(Aig_ManNodeNum(pAig1) == Aig_ManNodeNum(pAig2));

  Aig_Obj_t *pObj;
  int i;
  Aig_ManForEachCi(pAig1, pObj, i) Aig_ObjDbgCompare(pObj, Aig_ManCi(pAig2, i));
  Aig_ManForEachCo(pAig1, pObj, i) Aig_ObjDbgCompare(pObj, Aig_ManCo(pAig2, i));
  return true;
}

Aig_Man_t *Aig_ManSimplifyComb(Aig_Man_t *p) {
  AVY_MEASURE_FN;
  Dch_Pars_t pars;
  Dch_ManSetDefaultParams(&pars);
  pars.nWords = 16;
  Gia_Man_t *pGia = Gia_ManFromAigSimple(p);
  Gia_Man_t *pSynGia = Gia_ManCompress2(pGia, 1, 0);
  Gia_ManStop(pGia);
  Aig_Man_t *pSyn = Gia_ManToAigSimple(pSynGia);
  Gia_ManStop(pSynGia);
  return pSyn;
}

/** Add a primary input that causes the circuit to reset to the
 * initial state */
Aig_Man_t *Aig_AddResetPi(Aig_Man_t *p) {
  // Only support single property for now.
  AVY_ASSERT(p->nTruePos == 1 && "Assuming single PO");

  Aig_Man_t *pNew;
  Aig_Obj_t *pObj;
  int i;
  AVY_ASSERT(Aig_ManRegNum(p) > 0);
  // create the new manager
  pNew = Aig_ManStart(Aig_ManObjNumMax(p));
  pNew->pName = Abc_UtilStrsav(p->pName);
  pNew->pSpec = Abc_UtilStrsav(p->pSpec);
  pNew->nTruePis = p->nTruePis + 1;
  pNew->nTruePos = p->nTruePos;
  pNew->nRegs = p->nRegs;
  pNew->nConstrs = Saig_ManConstrNum(p);

  // create the PIs
  Aig_ManCleanData(p);
  Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
  Aig_Obj_t *pResetPi = Aig_ObjCreateCi(pNew);
  Aig_ManForEachCi(p, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);

  // duplicate internal nodes
  Aig_ManForEachNode(p, pObj, i) pObj->pData =
      Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));

  // -- re-create the single PO
  pObj = Aig_ManCo(p, 0);
  Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));

  // create constraint outputs
  Saig_ManForEachPo(p, pObj, i) {
    if (i < Saig_ManPoNum(p) - Saig_ManConstrNum(p))
      continue;
    Aig_ObjCreateCo(pNew, Aig_Not(Aig_ObjChild0Copy(pObj)));
  }

  // -- registers
  Saig_ManForEachLi(p, pObj, i) {
    Aig_Obj_t *pTmp = Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_Not(pResetPi));
    Aig_ObjCreateCo(pNew, pTmp);
  }

  Aig_ManCleanup(pNew);
  return pNew;
}

/** Add a Pi that causes the circuit to stutter (stay in the same
    state) */
Aig_Man_t *Aig_AddStutterPi(Aig_Man_t *p) {
  // Only support single property for now.
  AVY_ASSERT(p->nTruePos == 1 && "Assuming single PO");

  Aig_Man_t *pNew;
  Aig_Obj_t *pObj;
  int i;
  AVY_ASSERT(Aig_ManRegNum(p) > 0);
  // create the new manager
  pNew = Aig_ManStart(Aig_ManObjNumMax(p));
  pNew->pName = Abc_UtilStrsav(p->pName);
  pNew->pSpec = Abc_UtilStrsav(p->pSpec);
  pNew->nTruePis = p->nTruePis + 1;
  pNew->nTruePos = p->nTruePos;
  pNew->nRegs = p->nRegs;
  pNew->nConstrs = Saig_ManConstrNum(p);

  // create the PIs
  Aig_ManCleanData(p);
  Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
  Aig_Obj_t *pStutterPi = Aig_ObjCreateCi(pNew);
  Aig_ManForEachCi(p, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);

  // duplicate internal nodes
  Aig_ManForEachNode(p, pObj, i) pObj->pData =
      Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));

  // -- re-create the single PO
  pObj = Aig_ManCo(p, 0);
  Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pObj));

  // create constraint outputs
  Saig_ManForEachPo(p, pObj, i) {
    if (i < Saig_ManPoNum(p) - Saig_ManConstrNum(p))
      continue;
    Aig_ObjCreateCo(pNew, Aig_Not(Aig_ObjChild0Copy(pObj)));
  }

  // -- registers
  Aig_Obj_t *pLi;
  Saig_ManForEachLi(p, pLi, i) {
    Aig_Obj_t *pTmp =
        Aig_Mux(pNew, pStutterPi, Saig_ManLo(pNew, i), Aig_ObjChild0Copy(pLi));

    Aig_ObjCreateCo(pNew, pTmp);
  }

  Aig_ManCleanup(pNew);
  return pNew;
}

Aig_Man_t *Aig_AddStutterPo(Aig_Man_t *p) {
  // Only support single property for now.
  AVY_ASSERT(p->nTruePos == 1 && "Assuming single PO");

  Aig_Man_t *pNew;
  Aig_Obj_t *pObj;
  int i;
  AVY_ASSERT(Aig_ManRegNum(p) > 0);
  // create the new manager
  pNew = Aig_ManStart(Aig_ManObjNumMax(p));
  pNew->pName = Abc_UtilStrsav(p->pName);
  pNew->pSpec = Abc_UtilStrsav(p->pSpec);
  pNew->nTruePis = p->nTruePis;
  pNew->nTruePos = p->nTruePos;
  pNew->nRegs = p->nRegs + 1;
  pNew->nConstrs = Saig_ManConstrNum(p);

  // create the PIs
  Aig_ManCleanData(p);
  Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
  Aig_ManForEachCi(p, pObj, i) pObj->pData = Aig_ObjCreateCi(pNew);

  // -- create new register (last in the order of registers)
  Aig_Obj_t *pNewLo = Aig_ObjCreateCi(pNew);

  // duplicate internal nodes
  Aig_ManForEachNode(p, pObj, i) pObj->pData =
      Aig_And(pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj));

  // ----------------------------------------------------------------------
  // Outputs
  // ----------------------------------------------------------------------
  // -- re-create the single PO
  pObj = Aig_ManCo(p, 0);

  Aig_Obj_t *pNewPoDriver = Aig_ObjChild0Copy(pObj);
  // -- create PO with dummy driver
  Aig_Obj_t *pNewPo = Aig_ObjCreateCo(pNew, Aig_ManConst1(pNew));

  // create constraint outputs
  Saig_ManForEachPo(p, pObj, i) {
    if (i < Saig_ManPoNum(p) - Saig_ManConstrNum(p))
      continue;
    Aig_ObjCreateCo(pNew, Aig_Not(Aig_ObjChild0Copy(pObj)));
  }

  // -- registers
  Aig_Obj_t *pLi;
  Saig_ManForEachLi(p, pLi, i) Aig_ObjCreateCo(pNew, Aig_ObjChild0Copy(pLi));

  // -- new Li = newPoDriver || new Lo
  Aig_ObjCreateCo(pNew, Aig_Or(pNew, pNewLo, pNewPoDriver));
  // -- re-connect newPo
  Aig_ObjDisconnect(pNew, pNewPo);
  Aig_ObjConnect(pNew, pNewPo, Aig_Or(pNew, pNewLo, pNewPoDriver), NULL);

  Aig_ManCleanup(pNew);
  return pNew;
}

Aig_Man_t *Aig_CreateAllZero(unsigned nPiNum) {
  unsigned int i;
  AVY_ASSERT(nPiNum > 0);
  Aig_Obj_t **ppInputs = ABC_ALLOC(Aig_Obj_t *, nPiNum);
  Aig_Man_t *p = Aig_ManStart(nPiNum);
  for (i = 0; i < nPiNum; i++)
    ppInputs[i] = Aig_Not(Aig_ObjCreateCi(p));
  Aig_Obj_t *pRes = Aig_Multi(p, ppInputs, nPiNum, AIG_OBJ_AND);
  Aig_ObjCreateCo(p, pRes);
  ABC_FREE(ppInputs);
  return p;
}

/**
   Duplicate a given Aig while plugging optional values from vals
   for Ci

   vals.at(i) is the value of Ci i, such that
     vals.at(i) == true  ==> Ci(i) is true
     vals.at(i) == false ==> Ci(i) is false
     otherwise           ==> C(i)  is unchanged
 */
Aig_Man_t *Aig_DupWithCiVals(Aig_Man_t *p,
                             const std::vector<tribool> &vals) {
  Gia_Man_t *pGia = Gia_ManFromAigSimple(p);
  Gia_Man_t *pNewGia = Gia_DupWithCiVals(pGia, vals);
  Aig_Man_t *pNewAig = Gia_ManToAigSimple(pNewGia);
  Gia_ManStop(pGia);
  Gia_ManStop(pNewGia);
  pNewAig->nTruePis = p->nTruePis;
  pNewAig->nTruePos = p->nTruePos;
  Aig_ManCleanup(pNewAig);
  return pNewAig;
}

/**
   Duplicate a given Aig while plugging optional values from vals
   for Ci

   vals.at(i) is the value of Ci i, such that
     vals.at(i) == true  ==> Ci(i) is true
     vals.at(i) == false ==> Ci(i) is false
     otherwise           ==> C(i)  is unchanged
 */
// AG: Can this be implemented using Gia_DupWithCiEquivs by making Ci
// AG: equivalent to true/false
Gia_Man_t *Gia_DupWithCiVals(Gia_Man_t *p,
                             const std::vector<tribool> &vals) {
  Gia_Man_t *pNew;
  Gia_Obj_t *pObj;
  int i;
  pNew = Gia_ManStart(Gia_ManObjNum(p));
  Gia_ManHashStart(pNew);
  pNew->pName = Abc_UtilStrsav(p->pName);
  pNew->pSpec = Abc_UtilStrsav(p->pSpec);
  Gia_ManConst0(p)->Value = 0;
  unsigned nPiNum = Gia_ManPiNum(p);
  Gia_ManForEachCi(p, pObj, i) {
    pObj->Value = Gia_ManAppendCi(pNew);
    if (i >= nPiNum) {
      tribool val = vals[i - nPiNum];
      if (val)
        pObj->Value = Gia_ManConst1Lit();
      else if (!val)
        pObj->Value = Gia_ManConst0Lit();
    }
  }

  Gia_ManForEachAnd(p, pObj, i) {
    pObj->Value =
      Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
  }
  Gia_ManForEachCo(p, pObj, i) {
    pObj->Value = Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj));
  }
  Gia_ManDupRemapEquiv(pNew, p);
  Gia_ManSetRegNum(pNew, Gia_ManRegNum(p));
  AVY_ASSERT(Gia_ManIsNormalized(pNew));
  return pNew;
}

Gia_Man_t *Gia_DupWithCiEquivs(Gia_Man_t *p, const IntVector &equiv) {
  Gia_Man_t *pNew;
  Gia_Obj_t *pObj;
  int i;
  pNew = Gia_ManStart(Gia_ManObjNum(p));
  Gia_ManHashStart(pNew);
  pNew->pName = Abc_UtilStrsav(p->pName);
  pNew->pSpec = Abc_UtilStrsav(p->pSpec);
  Gia_ManConst0(p)->Value = 0;
  unsigned nPiNum = Gia_ManPiNum(p);
  Gia_ManForEachCi(p, pObj, i) {
    pObj->Value = Gia_ManAppendCi(pNew);
    if (i >= nPiNum) {
      int val = equiv[i - nPiNum];
      if (val == 0 || val == 1) {
        if (val == 1)
          pObj->Value = Gia_ManConst1Lit();
        else // if (val == 0)
          pObj->Value = Gia_ManConst0Lit();
      } else if (val != -1) {
        bool neg = (val < 0);
        if (val < 0)
          val *= -1;
        int loc = (val / 2) - 1;
        AVY_ASSERT(loc + nPiNum < i);
        pObj->Value = Abc_LitNotCond(Gia_ManCi(p, loc + nPiNum)->Value, neg);
        AVY_ASSERT(pObj->Value != 0);
      }
    }
  }

  Gia_ManForEachAnd(p, pObj, i) {
    pObj->Value =
      Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
  }
  Gia_ManForEachCo(p, pObj, i) {
    pObj->Value =
      Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj));
  }
  Gia_ManDupRemapEquiv(pNew, p);
  Gia_ManSetRegNum(pNew, Gia_ManRegNum(p));
  AVY_ASSERT(Gia_ManIsNormalized(pNew));
  return pNew;
}

Aig_Man_t *Aig_DupWithCiEquivs(Aig_Man_t *p, const IntVector &equiv) {
  Gia_Man_t *pGia = Gia_ManFromAigSimple(p);
  Gia_Man_t *pNewGia = Gia_DupWithCiEquivs(pGia, equiv);
  Aig_Man_t *pNewAig = Gia_ManToAigSimple(pNewGia);
  Gia_ManStop(pGia);
  Gia_ManStop(pNewGia);
  pNewAig->nTruePis = p->nTruePis;
  pNewAig->nTruePos = p->nTruePos;
  Aig_ManCleanup(pNewAig);

  return pNewAig;
}


Aig_Man_t *Aig_SatSweep(Aig_Man_t *p, IntVector &equivClasses) {

  Gia_Man_t *pGia = Gia_ManFromAigSimple(p);
  Cec_ParFra_t ParsFra;
  Cec_ManFraSetDefaultParams(&ParsFra);
  ParsFra.fSatSweeping = 1;
  ParsFra.fRewriting = 1;
  ParsFra.nItersMax = 4;
  ParsFra.fVerbose = 0;
  Gia_Man_t *pTemp = Cec_ManSatSweeping(pGia, &ParsFra, 0);
  Gia_ManStop(pGia);

  equivClasses.resize(p->nRegs, -1);
  int equiv = 0, neg_eq = 0;
  int consts = 0;
  int in_out = 0;
  int nPoNum = Gia_ManPoNum(pTemp);

  // iterate starting from last Co until first Po
  for (int i = Gia_ManCoNum(pTemp) - 1; i >= nPoNum; i--) {
    Gia_Obj_t *pObj = Gia_ManCo(pTemp, i);
    // check that Co is driven by Ci
    if (Gia_ObjIsCi(Gia_ObjFanin0(pObj))) in_out++;

    // First check if a constant
    if (Gia_Obj2Lit(pTemp, Gia_ObjFanin0(pObj)) == 0 ||
        Gia_Obj2Lit(pTemp, Gia_ObjFanin0(pObj)) == 1) {
      consts++;
      equivClasses[i - nPoNum] =
          Gia_Obj2Lit(pTemp, Gia_ObjChild0(pObj)) == 0 ? 0 : 1;
      continue;
    }
    // from Co before i down to first Po
    for (int j = i - 1; j >= nPoNum; j--) {
      if (Gia_ObjChild0(pObj) == Gia_ObjChild0(Gia_ManCo(pTemp, j)) ||
          Gia_ObjChild0(pObj) == Gia_Not(Gia_ObjChild0(Gia_ManCo(pTemp, j)))) {
        equiv++;
        if (Gia_ObjChild0(pObj) == Gia_ObjChild0(Gia_ManCo(pTemp, j)))
          // AG: encode j so that 0 and 1 are reserved for true/false
          // and -1 for unused
          equivClasses[i - nPoNum] = (j - nPoNum + 1) * 2; // Shift?
        else {
          equivClasses[i - nPoNum] = -((j - nPoNum + 1) * 2);
          neg_eq++;
        }

        break;
      }
    }
  }
  VERBOSE(3, vout() << "Found " << equiv << " (" << neg_eq << ")"
                    << " equiv and " << consts << " constans out of "
                    << Gia_ManCoNum(pTemp) << "\n"
                    << "Found output driven by intput: " << in_out << "\n";);
  Aig_Man_t *pNewAig = Gia_ManToAigSimple(pTemp);
  Gia_ManStop(pTemp);

  pNewAig->nTruePis = p->nTruePis;
  pNewAig->nTruePos = p->nTruePos;
  Aig_ManCleanup(pNewAig);
  AVY_ASSERT(equivClasses[0] == -1 || equivClasses[0] == 0 || equivClasses[0] == 1);
  return pNewAig;
}

Aig_Man_t *Aig_SatSweep(Aig_Man_t *p) {
  IntVector equivClasses;
  return Aig_SatSweep(p, equivClasses);
}


static void Aig_GetSupportRec(Aig_Man_t *pAig, Aig_Obj_t *pObj,
                              IntVector &drivingRoots) {
  if (pObj->fMarkA) return;
  pObj->fMarkA = 1;

  if (Aig_ObjIsAnd(pObj)) {
    Aig_GetSupportRec(pAig, Aig_ObjFanin0(pObj), drivingRoots);
    Aig_GetSupportRec(pAig, Aig_ObjFanin1(pObj), drivingRoots);
  } else if (Aig_ObjIsCi(pObj)) {
    if (Aig_ObjCioId(pObj) >= pAig->nTruePis)
      drivingRoots.push_back(Aig_ObjCioId(pObj) - pAig->nTruePis);
  } else {
    AVY_ASSERT(Aig_ObjIsConst1(Aig_Regular(pObj)));
  }
}

void Aig_GetSupport(Aig_Man_t *pAig, const IntVector &startingRoots,
                      IntVector &drivingRoots) {
  Aig_ManCleanMarkA(pAig);
  unsigned nSize = startingRoots.size();
  for (unsigned i = 0; i < nSize; i++) {
    AVY_ASSERT(startingRoots[i] < Aig_ManCoNum(pAig));
    Aig_Obj_t *pObj = Aig_ManCo(pAig, startingRoots[i]);
    Aig_GetSupportRec(pAig, Aig_ObjFanin0(pObj), drivingRoots);
  }
  Aig_ManCleanMarkA(pAig);
}
} // namespace avy
