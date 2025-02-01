#include "ItpCadical.h"
#include "AigPrint.h"
#include "aig/gia/giaAig.h"
#include "misc/vec/vec.h"

#include "AvyTypes.h" //IntVector
#include "CadicalItpSeq.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"

namespace avy {
/// Compute an interpolant. User provides the list of shared variables
/// Variables can only be shared between adjacent partitions.
/// fMcM == true for McMillan, and false for McMillan'
Aig_Man_t *ItpCadical::getInterpolant(int bad,
                                      std::vector<Vec_Int_t *> &vSharedVars,
                                      int nNumOfVars, bool fMcM) {
  AVY_MEASURE_FN;
  // AVY_ASSERT (!isTrivial ());
  AVY_ASSERT(m_pSat != NULL);
  AVY_ASSERT(vSharedVars.size() >= m_nParts - 1);

  IntVector assump;
  assump.push_back(bad);
  // AVY_VERIFY (!solve (assump));

  IntVector vVarToId;
  BOOST_FOREACH (Vec_Int_t *vVec, vSharedVars) {
    int nVar;
    int i;
    Vec_IntForEachEntry(vVec, nVar, i) {
      if (nVar != -1) {
        // -- resize (not needed if we know how many variables there are)
        if (vVarToId.size() <= nVar) vVarToId.resize(nVar + 1, -1);
        vVarToId[nVar] = i;
      }
    }
  }

  if (gParams.cadical_itp_minimize) {
    const auto vars = m_pSat->vars();
    MinimizerReplay minimizer(vars, gParams.cadical_itp_minimizer_preprocessing, gParams.cadical_itp_minimizer_inprocessing);
    DRUP2ITP::MiniTracer mini_tracer = minimizer.mini_tracer();
    CadicalItpSeq proof_it(vars, nNumOfVars, vVarToId, m_nParts - 1,
                           m_Assumptions, mini_tracer);
    AVY_VERIFY(m_tracer->trim(&minimizer, true /* undo */));
    minimizer.replay(proof_it);

    Gia_Man_t *pManGia = Gia_ManRehash(proof_it.getInterpolantMan(), 1);
    Aig_Man_t *pMan = Gia_ManToAigSimple(pManGia);

    Gia_ManHashStop(pManGia);
    Gia_ManStop(pManGia);

    VERBOSE(2, Aig_ManPrintStats(pMan););
    LOG("itp_verbose", logs() << *pMan << "\n";);
    std::string vv(m_pSat->version());
    LOG("CADICAL-VERSION", logs() << vv.c_str() << "\n";);
    // Release memory
    // Sto_ManFree( pSatCnf );
    return pMan;
  } else {
    DRUP2ITP::MiniTracer mini_tracer = m_tracer->mini_tracer();
    CadicalItpSeq proof_it(m_pSat->vars(), nNumOfVars, vVarToId, m_nParts - 1,
                           m_Assumptions, mini_tracer);
    AVY_VERIFY(m_tracer->trim(nullptr, false /* incremental */));
    m_tracer->replay(proof_it, true /* incremental */);

    Gia_Man_t *pManGia = Gia_ManRehash(proof_it.getInterpolantMan(), 1);
    Aig_Man_t *pMan = Gia_ManToAigSimple(pManGia);

    Gia_ManHashStop(pManGia);
    Gia_ManStop(pManGia);

    VERBOSE(2, Aig_ManPrintStats(pMan););
    LOG("itp_verbose", logs() << *pMan << "\n";);
    // Release memory
    // Sto_ManFree( pSatCnf );
    return pMan;
  }
}

} // namespace avy
