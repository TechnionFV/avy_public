#include "avy/Util/Global.h"

namespace avy {
AvyParams gParams;

std::ostream &operator<<(std::ostream &out, const AvyParams &p) {
  out << "AVY PARAMETERS\n"
      << "\tfName = " << p.fName << "\n"
      << "\tipt = " << p.itp << "\n"
      << "\tavy = " << p.avy << "\n"
      << "\tstutter = " << p.stutter << "\n"
      << "\treset-cover = " << p.reset_cover << "\n"
      << "\tshallow_push = " << p.shallow_push << "\n"
      << "\tmin-core = " << p.min_core << "\n"
      << "\tabstraction = " << p.abstraction << "\n"
      << "\ttr0 = " << p.tr0 << "\n"
      << "\tpdr = " << p.pdr << "\n"
      << "\tmin-suffix = " << p.min_suffix << "\n"
      << "\tsat1 = " << p.sat1 << "\n"
      << "\tminisat = " << p.minisat << "\n"
      << "\tglucose = " << p.glucose << "\n"
      << "\tminisat_itp = " << p.minisat_itp << "\n"
      << "\tcadical_itp = " << p.cadical_itp << "\n"
      << "\tcadical_itp_minimize = " << p.cadical_itp_minimize << "\n"
      << "\tcadical_itp_inprocessing = " << p.cadical_itp_inprocessing << "\n"
      << "\tcadical_itp_minimizer_inprocessing = " << p.cadical_itp_minimizer_inprocessing << "\n"
      << "\tcadical_itp_minimizer_preprocessing = " << p.cadical_itp_minimizer_preprocessing << "\n"
      << "\tglucose_itp = " << p.glucose_itp << "\n"
      << "\tsat_simp = " << p.sat_simp << "\n"
      << "\titp_simp = " << p.itp_simp << "\n"
      << "\tproof_reorder = " << p.proof_reorder << "\n"
      << "\tgen-conf-limit = " << p.genConfLimit << "\n"
      << "\tkstep = " << p.kStep << "\n"
      << "\tstick-error = " << p.stick_error << "\n"
      << "\titp-simplify = " << p.itp_simplify << "\n"
      << "\tmax-frame = " << p.maxFrame << "\n"
      << "\tmin-core-muser = " << p.min_muser << "\n"
      << "\tincr = " << p.incr << "\n"
      << "END";
  return out;
}

} // namespace avy
