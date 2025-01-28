#include "AigPrint.h"
#include "avy/AvyAbc.h"
#include "avy/Util/AvyAssert.h"

namespace avy {
using namespace avy::abc;
using namespace avy_abc_pdr;

namespace {
void Aig_PrintVerilog(std::ostream &out, Aig_Man_t *pMan, Aig_Obj_t *pObj,
                      Vec_Vec_t *vLevels, int Level) {
  Vec_Ptr_t *vSuper;
  Aig_Obj_t *pFanin, *pFanin0, *pFanin1, *pFaninC;
  int fCompl, i;
  // store the complemented attribute
  fCompl = Aig_IsComplement(pObj);
  pObj = Aig_Regular(pObj);
  // constant case
  if (Aig_ObjIsConst1(pObj)) {
    out << (fCompl ? "false" : "true");
    return;
  }
  // PI case
  if (Aig_ObjIsCi(pObj)) {
    if (fCompl)
      out << "~";
    if (Saig_ObjIsPi(pMan, pObj))
      out << "v" << pObj->Id;
    else {
      AVY_ASSERT(Saig_ObjIsLo(pMan, pObj));
      out << "lo" << Saig_ObjRegId(pMan, pObj);
    }
    return;
  }
  // EXOR case
  if (Aig_ObjIsExor(pObj)) {
    Vec_VecExpand(vLevels, Level);
    vSuper = Vec_VecEntry(vLevels, Level);
    Aig_ObjCollectMulti(pObj, vSuper);
    if (Level > 0)
      out << "(";
    Vec_PtrForEachEntry(Aig_Obj_t *, vSuper, pFanin, i) {
      Aig_PrintVerilog(out, pMan, Aig_NotCond(pFanin, (fCompl && i == 0)),
                       vLevels, Level + 1);
      if (i < Vec_PtrSize(vSuper) - 1)
        out << " ^ ";
    }
    if (Level > 0)
      out << ")";
    return;
  }
  // MUX case
  if (Aig_ObjIsMuxType(pObj)) {
    if (Aig_ObjRecognizeExor(pObj, &pFanin0, &pFanin1)) {
      if (Level > 0)
        out << "(";
      Aig_PrintVerilog(out, pMan, Aig_NotCond(pFanin0, fCompl), vLevels,
                       Level + 1);
      out << " ^ ";
      Aig_PrintVerilog(out, pMan, pFanin1, vLevels, Level + 1);
      if (Level > 0)
        out << ")";
    } else {
      pFaninC = Aig_ObjRecognizeMux(pObj, &pFanin1, &pFanin0);
      if (Level > 0)
        out << "(";
      Aig_PrintVerilog(out, pMan, pFaninC, vLevels, Level + 1);
      out << " ? ";
      Aig_PrintVerilog(out, pMan, Aig_NotCond(pFanin1, fCompl), vLevels,
                       Level + 1);
      out << " : ";
      Aig_PrintVerilog(out, pMan, Aig_NotCond(pFanin0, fCompl), vLevels,
                       Level + 1);
      if (Level > 0)
        out << ")";
    }
    return;
  }
  // AND case
  Vec_VecExpand(vLevels, Level);
  vSuper = Vec_VecEntry(vLevels, Level);
  Aig_ObjCollectMulti(pObj, vSuper);
  if (Level > 0)
    out << "(";
  Vec_PtrForEachEntry(Aig_Obj_t *, vSuper, pFanin, i) {
    Aig_PrintVerilog(out, pMan, Aig_NotCond(pFanin, fCompl), vLevels,
                     Level + 1);
    if (i < Vec_PtrSize(vSuper) - 1)
      out << (fCompl ? " | " : " & ");
  }
  if (Level > 0)
    out << ")";
  return;
}
} // namespace

std::ostream &PrintAig(std::ostream &out, Aig_Man_t *pMan, Aig_Obj_t *pObj) {
  AVY_ASSERT(!Aig_ObjIsCo(pObj));

  Vec_Vec_t *vVec = Vec_VecAlloc(10);
  Aig_PrintVerilog(out, pMan, pObj, vVec, 0);
  return out;
}

std::ostream &PrintAigMan(std::ostream &out, Aig_Man_t *pMan) {
  Aig_Obj_t *pObj;
  int i;

  out << "AIG BEGIN\n";
  Saig_ManForEachPo(pMan, pObj, i) {
    out << "po" << i << " := ";
    PrintAig(out, pMan, Aig_ObjChild0(pObj));
    out << "\n";
  }
  Saig_ManForEachLi(pMan, pObj, i) {
    out << "li" << i << " := ";
    PrintAig(out, pMan, Aig_ObjChild0(pObj));
    out << "\n";
  }

  out << "AIG END\n";
  return out;
}

std::ostream &PrintPdrSet(std::ostream &out, Pdr_Set_t *pCube) {
  for (int i = 0; i < pCube->nLits; ++i) {
    if (lit_sign(pCube->Lits[i]))
      out << "-";

    out << lit_var(pCube->Lits[i]) << " ";
  }
  return out;
}

std::ostream &PrintPdrSets(std::ostream &out, Vec_Ptr_t &cubes) {
  Vec_Ptr_t *pCubes = &cubes;

  int j;
  Pdr_Set_t *pCube;
  out << "CUBES BEGIN\n";
  Vec_PtrForEachEntry(Pdr_Set_t *, pCubes, pCube, j) out << j << ": " << *pCube
                                                         << "\n";
  out << "CUBES END\n";
  return out;
}

} // namespace avy
