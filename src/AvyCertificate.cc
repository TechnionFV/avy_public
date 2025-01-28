//
// Created by Yakir Vizel on 8/25/24.
//

#include "AvyMain.h"
#include "aig/gia/giaAig.h"
#include "base/main/main.h"

using namespace avy;

void AvyMain::printInvCert(const std::string & certificate_filename)
{
    Aig_Man_t *pAig = Aig_ManStart(10000);

    unsigned numRegs = Aig_ManRegNum(m_Aig.get());
    unsigned numPIs = Aig_ManCiNum(m_Aig.get()) - numRegs;
    for(unsigned i=0; i <  numRegs; i++)
    {
        Aig_ObjCreateCi(pAig);
    }

    Vec_Ptr_t *pInvar = Vec_PtrAlloc(16);;
    m_pPdr->getInvarCubes(pInvar);

    Pdr_Set_t *pCube;
    unsigned j;
    Aig_Obj_t *pInv = Aig_ManConst1(pAig);
    Vec_PtrForEachEntry(Pdr_Set_t *, pInvar, pCube, j) {
        Aig_Obj_t *pCls = Aig_ManConst0(pAig);
        for (unsigned i = 0; i < pCube->nLits; i++ ) {
            if (pCube->Lits[i] == -1)
                continue;
            AVY_ASSERT(lit_var(pCube->Lits[i]) < numRegs);
            Aig_Obj_t *pObj = Aig_ManCi(pAig, lit_var(pCube->Lits[i]));
            pCls = Aig_Or(pAig, pCls, (lit_sign(pCube->Lits[i])) ? pObj : Aig_Not(pObj));
        }

        pInv = Aig_And(pAig, pInv, pCls);
    }

    Aig_ObjCreateCo(pAig, Aig_Not(pInv));

    Aig_Man_t *pNew = Aig_ManReplacePo(m_Aig.get(), pAig, 0);

    Gia_Man_t *p = Gia_ManFromAigSimple(pNew);
    Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();
    Abc_FrameUpdateGia(pFrame, p);
    Cmd_CommandExecute(pFrame, std::string("&put; write_aiger " + certificate_filename).c_str());

    Vec_PtrClear(pInvar);
    Vec_PtrFree(pInvar);

    Aig_ManStop(pAig);
}