
#include "CnfUtils.h"

namespace ABC_NAMESPACE {
    extern int Cnf_SopCountLiterals( char * pSop, int nCubes);
    extern int Cnf_IsopCountLiterals( Vec_Int_t * vIsop, int nVars );
    extern int Cnf_IsopWriteCube( int Cube, int nVars, int * pVars, int * pLiterals );
} // namespace ABC_NAMESPACE

using namespace avy::abc;

namespace avy {
/**Function*************************************************************

  Synopsis    [Derives CNF for the mapping.]

  Description [The last argument shows the number of last outputs
  of the manager, which will not be converted into clauses but the
  new variables for which will be introduced.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Cnf_Dat_t *Cnf_ManWriteCnf_withClsMappings(Cnf_Man_t *p, Vec_Ptr_t *vMapped, int nOutputs) {
    int fChangeVariableOrder = 0; // should be set to 0 to improve performance
    Aig_Obj_t *pObj;
    Cnf_Dat_t *pCnf;
    Cnf_Cut_t *pCut;
    Vec_Int_t *vCover, *vSopTemp;
    int OutVar, PoVar, pVars[32], *pLits, **pClas;
    unsigned uTruth;
    int i, k, nLiterals, nClauses, Cube, Number;

    // count the number of literals and clauses
    nLiterals = 1 + Aig_ManCoNum(p->pManAig) + 3 * nOutputs;
    nClauses = 1 + Aig_ManCoNum(p->pManAig) + nOutputs;
    Vec_PtrForEachEntry(Aig_Obj_t * , vMapped, pObj, i)
    {
        assert(Aig_ObjIsNode(pObj));
        pCut = Cnf_ObjBestCut(pObj);

        // positive polarity of the cut
        if (pCut->nFanins < 5) {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            nLiterals += Cnf_SopCountLiterals(p->pSops[uTruth], p->pSopSizes[uTruth]) + p->pSopSizes[uTruth];
            assert(p->pSopSizes[uTruth] >= 0);
            nClauses += p->pSopSizes[uTruth];
        } else {
            nLiterals += Cnf_IsopCountLiterals(pCut->vIsop[1], pCut->nFanins) + Vec_IntSize(pCut->vIsop[1]);
            nClauses += Vec_IntSize(pCut->vIsop[1]);
        }
        // negative polarity of the cut
        if (pCut->nFanins < 5) {
            uTruth = 0xFFFF & ~*Cnf_CutTruth(pCut);
            nLiterals += Cnf_SopCountLiterals(p->pSops[uTruth], p->pSopSizes[uTruth]) + p->pSopSizes[uTruth];
            assert(p->pSopSizes[uTruth] >= 0);
            nClauses += p->pSopSizes[uTruth];
        } else {
            nLiterals += Cnf_IsopCountLiterals(pCut->vIsop[0], pCut->nFanins) + Vec_IntSize(pCut->vIsop[0]);
            nClauses += Vec_IntSize(pCut->vIsop[0]);
        }
//printf( "%d ", nClauses-(1 + Aig_ManCoNum( p->pManAig )) );
    }
//printf( "\n" );

    // allocate CNF
    pCnf = ABC_CALLOC(Cnf_Dat_t, 1);
    pCnf->pMan = p->pManAig;
    pCnf->nLiterals = nLiterals;
    pCnf->nClauses = nClauses;
    pCnf->pClauses = ABC_ALLOC(int * , nClauses + 1);
    pCnf->pClauses[0] = ABC_ALLOC(int, nLiterals);
    pCnf->pClauses[nClauses] = pCnf->pClauses[0] + nLiterals;
    // create room for variable numbers
    pCnf->pObj2Clause = ABC_ALLOC(int, Aig_ManObjNumMax(p->pManAig));
    pCnf->pObj2Count = ABC_ALLOC(int, Aig_ManObjNumMax(p->pManAig));
    for (i = 0; i < Aig_ManObjNumMax(p->pManAig); i++)
        pCnf->pObj2Clause[i] = pCnf->pObj2Count[i] = -1;
    pCnf->pVarNums = ABC_ALLOC(int, Aig_ManObjNumMax(p->pManAig));
//    memset( pCnf->pVarNums, 0xff, sizeof(int) * Aig_ManObjNumMax(p->pManAig) );
    for (i = 0; i < Aig_ManObjNumMax(p->pManAig); i++)
        pCnf->pVarNums[i] = -1;

    // clear the PI counters
    Aig_ManForEachCi(p->pManAig, pObj, i)
    pCnf->pObj2Count[pObj->Id] = 0;

    if (!fChangeVariableOrder) {
        // assign variables to the last (nOutputs) POs
        Number = 1;
        if (nOutputs) {
            if (Aig_ManRegNum(p->pManAig) == 0) {
                assert(nOutputs == Aig_ManCoNum(p->pManAig));
                Aig_ManForEachCo(p->pManAig, pObj, i)
                pCnf->pVarNums[pObj->Id] = Number++;
            } else {
                assert(nOutputs == Aig_ManRegNum(p->pManAig));
                Aig_ManForEachLiSeq(p->pManAig, pObj, i)
                pCnf->pVarNums[pObj->Id] = Number++;
            }
        }
        // assign variables to the internal nodes
        Vec_PtrForEachEntry(Aig_Obj_t * , vMapped, pObj, i)
        pCnf->pVarNums[pObj->Id] = Number++;
        // assign variables to the PIs and constant node
        Aig_ManForEachCi(p->pManAig, pObj, i)
        pCnf->pVarNums[pObj->Id] = Number++;
        pCnf->pVarNums[Aig_ManConst1(p->pManAig)->Id] = Number++;
        pCnf->nVars = Number;
    } else {
        // assign variables to the last (nOutputs) POs
        Number = Aig_ManObjNumMax(p->pManAig) + 1;
        pCnf->nVars = Number + 1;
        if (nOutputs) {
            if (Aig_ManRegNum(p->pManAig) == 0) {
                assert(nOutputs == Aig_ManCoNum(p->pManAig));
                Aig_ManForEachCo(p->pManAig, pObj, i)
                pCnf->pVarNums[pObj->Id] = Number--;
            } else {
                assert(nOutputs == Aig_ManRegNum(p->pManAig));
                Aig_ManForEachLiSeq(p->pManAig, pObj, i)
                pCnf->pVarNums[pObj->Id] = Number--;
            }
        }
        // assign variables to the internal nodes
        Vec_PtrForEachEntry(Aig_Obj_t * , vMapped, pObj, i)
        pCnf->pVarNums[pObj->Id] = Number--;
        // assign variables to the PIs and constant node
        Aig_ManForEachCi(p->pManAig, pObj, i)
        pCnf->pVarNums[pObj->Id] = Number--;
        pCnf->pVarNums[Aig_ManConst1(p->pManAig)->Id] = Number--;
        assert(Number >= 0);
    }

    // assign the clauses
    vSopTemp = Vec_IntAlloc(1 << 16);
    pLits = pCnf->pClauses[0];
    pClas = pCnf->pClauses;
    Vec_PtrForEachEntry(Aig_Obj_t * , vMapped, pObj, i)
    {
        // remember the starting clause
        pCnf->pObj2Clause[pObj->Id] = pClas - pCnf->pClauses;
        pCnf->pObj2Count[pObj->Id] = 0;

        pCut = Cnf_ObjBestCut(pObj);

        // save variables of this cut
        OutVar = pCnf->pVarNums[pObj->Id];
        for (k = 0; k < (int) pCut->nFanins; k++) {
            pVars[k] = pCnf->pVarNums[pCut->pFanins[k]];
            assert(pVars[k] <= Aig_ManObjNumMax(p->pManAig));
        }

        // positive polarity of the cut
        if (pCut->nFanins < 5) {
            uTruth = 0xFFFF & *Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector(p->pSops[uTruth], p->pSopSizes[uTruth], vSopTemp);
            vCover = vSopTemp;
        } else
            vCover = pCut->vIsop[1];
        Vec_IntForEachEntry(vCover, Cube, k)
        {
            *pClas++ = pLits;
            *pLits++ = 2 * OutVar;
            pLits += Cnf_IsopWriteCube(Cube, pCut->nFanins, pVars, pLits);
        }
        pCnf->pObj2Count[pObj->Id] += Vec_IntSize(vCover);

        // negative polarity of the cut
        if (pCut->nFanins < 5) {
            uTruth = 0xFFFF & ~*Cnf_CutTruth(pCut);
            Cnf_SopConvertToVector(p->pSops[uTruth], p->pSopSizes[uTruth], vSopTemp);
            vCover = vSopTemp;
        } else
            vCover = pCut->vIsop[0];
        Vec_IntForEachEntry(vCover, Cube, k)
        {
            *pClas++ = pLits;
            *pLits++ = 2 * OutVar + 1;
            pLits += Cnf_IsopWriteCube(Cube, pCut->nFanins, pVars, pLits);
        }
        pCnf->pObj2Count[pObj->Id] += Vec_IntSize(vCover);
    }
    Vec_IntFree(vSopTemp);

    // write the constant literal
    OutVar = pCnf->pVarNums[Aig_ManConst1(p->pManAig)->Id];
    assert(OutVar <= Aig_ManObjNumMax(p->pManAig));
    *pClas++ = pLits;
    *pLits++ = 2 * OutVar;

    // write the output literals
    Aig_ManForEachCo(p->pManAig, pObj, i)
    {
        // remember the starting clause
        pCnf->pObj2Clause[pObj->Id] = pClas - pCnf->pClauses;
        pCnf->pObj2Count[pObj->Id] = 2;

        OutVar = pCnf->pVarNums[Aig_ObjFanin0(pObj)->Id];
        if (i < Aig_ManCoNum(p->pManAig) - nOutputs) {
            *pClas++ = pLits;
            *pLits++ = 2 * OutVar + Aig_ObjFaninC0(pObj);
        } else {
            PoVar = pCnf->pVarNums[pObj->Id];
            // first clause
            *pClas++ = pLits;
            *pLits++ = 2 * PoVar;
            *pLits++ = 2 * OutVar + !Aig_ObjFaninC0(pObj);
            // second clause
            *pClas++ = pLits;
            *pLits++ = 2 * PoVar + 1;
            *pLits++ = 2 * OutVar + Aig_ObjFaninC0(pObj);
        }
    }
    // remember the starting clause
    pCnf->pObj2Clause[Aig_ManConst1(p->pManAig)->Id] = pClas - pCnf->pClauses;
    pCnf->pObj2Count[Aig_ManConst1(p->pManAig)->Id] = 1;

    // verify that the correct number of literals and clauses was written
    assert(pLits - pCnf->pClauses[0] == nLiterals);
    assert(pClas - pCnf->pClauses == nClauses);
//Cnf_DataPrint( pCnf, 1 );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    [Converts AIG into the SAT solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Cnf_Dat_t * Cnf_DeriveWithMan_withClsMappings( Cnf_Man_t * p, Aig_Man_t * pAig, int nOutputs )
{
    Cnf_Dat_t * pCnf;
    Vec_Ptr_t * vMapped;
    Aig_MmFixed_t * pMemCuts;
    abctime clk;
    // connect the managers
    p->pManAig = pAig;

    // generate cuts for all nodes, assign cost, and find best cuts
    clk = Abc_Clock();
    pMemCuts = Dar_ManComputeCuts( pAig, 10, 0, 0 );
    p->timeCuts = Abc_Clock() - clk;

    // find the mapping
    clk = Abc_Clock();
    Cnf_DeriveMapping( p );
    p->timeMap = Abc_Clock() - clk;
//    Aig_ManScanMapping( p, 1 );

    // convert it into CNF
    clk = Abc_Clock();
    Cnf_ManTransferCuts( p );
    vMapped = Cnf_ManScanMapping( p, 1, 1 );
    pCnf = Cnf_ManWriteCnf_withClsMappings( p, vMapped, nOutputs );
    Vec_PtrFree( vMapped );
    Aig_MmFixedStop( pMemCuts, 0 );
    p->timeSave = Abc_Clock() - clk;

    // reset reference counters
    Aig_ManResetRefs( pAig );
//ABC_PRT( "Cuts   ", p->timeCuts );
//ABC_PRT( "Map    ", p->timeMap  );
//ABC_PRT( "Saving ", p->timeSave );
    return pCnf;
}

Cnf_Dat_t * AvyCnf_Derive( Aig_Man_t * pAig, int nOutputs )
{
    Cnf_ManPrepare();
    return Cnf_DeriveWithMan_withClsMappings( Cnf_ManRead(), pAig, nOutputs );
}

}