/**CFile****************************************************************

  FileName    [pdr.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property driven reachability.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2010.]

  Revision    [$Id: pdr.h,v 1.00 2010/11/20 00:00:00 alanmi Exp $]

***********************************************************************/

#pragma once

namespace avy_abc_pdr {
using namespace ABC_NAMESPACE;

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Pdr_Par_t_ Pdr_Par_t;
struct Pdr_Par_t_
{
//    int iOutput;          // zero-based number of primary output to solve
    int nRecycle;         // limit on vars for recycling
    int nFrameMax;        // limit on frame count
    int nConfLimit;       // limit on SAT solver conflicts
    int nRestLimit;       // limit on the number of proof-obligations
    int nTimeOut;         // timeout in seconds
    int nTimeOutGap;      // approximate timeout in seconds since the last change
    int nTimeOutOne;      // approximate timeout in seconds per one output
    int fTwoRounds;       // use two rounds for generalization
    int fMonoCnf;         // monolythic CNF
    int fDumpInv;         // dump inductive invariant
    int fShortest;        // forces bug traces to be shortest
    int fSkipGeneral;     // skips expensive generalization step
    int fVerbose;         // verbose output`
    int fVeryVerbose;     // very verbose output
    int fNotVerbose;      // not printing line by line progress
    int fSilent;          // totally silent execution
    int fSolveAll;        // do not stop when found a SAT output
    int fStoreCex;        // enable storing counter-examples in MO mode
    int nFailOuts;        // the number of failed outputs
    int nDropOuts;        // the number of timed out outputs
    int nProveOuts;       // the number of proved outputs
    int iFrame;           // explored up to this frame
    int RunId;            // PDR id in this run
    int(*pFuncStop)(int); // callback to terminate
    int(*pFuncOnFail)(int,Abc_Cex_t*); // called for a failed output in MO mode
    abctime timeLastSolved; // the time when the last output was solved
    Vec_Int_t * vOutMap;  // in the multi-output mode, contains status for each PO (0 = sat; 1 = unsat; negative = undecided)
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== pdrCore.c ==========================================================*/
extern void               Pdr_ManSetDefaultParams( Pdr_Par_t * pPars );
extern int                Pdr_ManSolve( Aig_Man_t * p, Pdr_Par_t * pPars );


}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
