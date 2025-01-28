#include "ItpGlucose.h"
#include "AigPrint.h"
#include "aig/gia/giaAig.h"
#include "misc/vec/vec.h"

#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"
#include "AvyTypes.h" //IntVector
#include "GlucoseItpSeq.h"

namespace avy {
/// Compute an interpolant. User provides the list of shared variables
/// Variables can only be shared between adjacent partitions.
/// fMcM == true for McMillan, and false for McMillan'
Aig_Man_t *ItpGlucose::getInterpolant(lit bad,
                                      std::vector<Vec_Int_t *> &vSharedVars,
                                      int nNumOfVars, bool fMcM) {
  AVY_MEASURE_FN;
  // AVY_ASSERT (!isTrivial ());
  AVY_ASSERT(m_pSat != NULL);
  AVY_ASSERT(vSharedVars.size() >= m_nParts - 1);

  // IntVector assump;
  // assump.push_back(bad);
  IntVector vVarToId;

  for (Vec_Int_t *vVec : vSharedVars) {
    int nVar;
    int i;
    Vec_IntForEachEntry(vVec, nVar, i) {
      if (nVar != -1) {
        // -- resize (not needed if we know how many variables there are)
        if (vVarToId.size() <= nVar)
          vVarToId.resize(nVar + 1, -1);
        vVarToId[nVar] = i;
      }
    }
  }

  GlucoseItpSeq itpSeqVisitor(*m_pSat, nNumOfVars, vVarToId, m_nParts - 1);
  AVY_VERIFY(m_pSat->validate());
  m_pSat->replay(itpSeqVisitor);

  Gia_Man_t *pManGia = Gia_ManRehash(itpSeqVisitor.getInterpolantMan(), 1);
  Aig_Man_t *pMan = Gia_ManToAigSimple(pManGia);

  Gia_ManHashStop(pManGia);
  Gia_ManStop(pManGia);

  VERBOSE(2, Aig_ManPrintStats(pMan););
  LOG("itp_verbose", logs() << *pMan << "\n";);

  // Release memory
  // Sto_ManFree( pSatCnf );
  return pMan;
}

} // namespace avy
