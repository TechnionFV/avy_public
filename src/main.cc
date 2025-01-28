/*
 * main.cc
 *
 *  Created on: Jul 29, 2013
 *      Author: yakir
 */

#include <cstdlib>
#include <iostream>
#include <vector>

#include "boost/dynamic_bitset.hpp"
#include "boost/program_options.hpp"
namespace po = boost::program_options;

#include "AvyMain.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"

#include "BuildVariables.inc"

using namespace std;
using namespace avy;

std::string parseCmdLine(int argc, char **argv) {
  po::options_description generic("Options");
  generic.add_options()("help", "produce help message")(
      "print-params", "print current parameters")(
      "log,L", po::value<vector<string>>(), "log levels to enable")(
      "itp", po::value<unsigned>(&gParams.itp)->default_value(0),
      "Interpolation system: 0 - McM, 1 - Mcm-prime")(
      "verbose,v", po::value<unsigned>(&gParams.verbosity)->default_value(0),
      "Verbosity level: 0 means silent")("version", "Print version string")(
      "avy",
      po::value<bool>(&gParams.avy)->implicit_value(true)->default_value(true))(
      "stutter,s",
      po::value<bool>(&gParams.stutter)
          ->default_value(false)
          ->implicit_value(true),
      "Stutter circuit instead of reseting to the initial state")(
      "reset-cover",
      po::value<bool>(&gParams.reset_cover)
          ->default_value(false)
          ->implicit_value(true),
      "Reset cover of global PDR before updating it")(
      "shallow-push",
      po::value<bool>(&gParams.shallow_push)
          ->default_value(false)
          ->implicit_value(true),
      "Push only updated covers")("min-core",
                                  po::value<bool>(&gParams.min_core)
                                      ->default_value(false)
                                      ->implicit_value(true),
                                  "Minimize unsat core")(
      "min-core-muser",
      po::value<bool>(&gParams.min_muser)
          ->default_value(false)
          ->implicit_value(true),
      "Minimize unsat core using muser tool")("lemma-abs",
                                              po::value<bool>(&gParams.lemmaAbs)
                                                  ->default_value(false)
                                                  ->implicit_value(true),
                                              "Abstraction for lemmas")(
      "incr",
      po::value<bool>(&gParams.incr)
          ->default_value(false)
          ->implicit_value(true),
      "load clauses to solver incrementally")(
      "coi",
      po::value<bool>(&gParams.coi)->default_value(true)->implicit_value(true),
      "only add clauses in the COI to the solver")(
      "abstraction,a",
      po::value<bool>(&gParams.abstraction)
          ->default_value(false)
          ->implicit_value(true),
      "Enable interface abstraction (one-assumption-per-wire)")(
      "tr0",
      po::value<bool>(&gParams.tr0)->default_value(false)->implicit_value(true),
      "Make only Tr0 be special (stutter or reset init)")(
      "pdr", po::value<int>(&gParams.pdr)->default_value(100000),
      "Frame at which to drop to PDR")(
      "min-suffix",
      po::value<bool>(&gParams.min_suffix)
          ->default_value(false)
          ->implicit_value(true),
      "Minimize the suffix of the interpolation sequence")(
      "sat1",
      po::value<bool>(&gParams.sat1)
          ->default_value(false)
          ->implicit_value(true),
      "Always use satSolver (do not use satSolver2)")(
      "minisat",
      po::value<bool>(&gParams.minisat)
          ->default_value(false)
          ->implicit_value(true),
      "Use Minisat 2.2.0 for abstraction")("glucose",
                                           po::value<bool>(&gParams.glucose)
                                               ->default_value(true)
                                               ->implicit_value(true),
                                           "Use Glucose for abstraction")(
      "minisat_itp",
      po::value<bool>(&gParams.minisat_itp)
          ->default_value(false)
          ->implicit_value(true),
      "Use Minisat 2.2.0 for interpolation")(
        "cadical_itp_minimize",
        po::value<bool>(&gParams.cadical_itp_minimize)
                ->default_value(false)
                ->implicit_value(true),
        "Use CaDiCal DRUP2ITP Minimizer")(
        "cadical_itp_inprocessing",
        po::value<bool>(&gParams.cadical_itp_inprocessing)
                ->default_value(false)
                ->implicit_value(true),
        "Set inprocessing in CaDiCal DRUP2ITP for interpolation")(
        "cadical_itp_minimizer_inprocessing",
        po::value<bool>(&gParams.cadical_itp_minimizer_inprocessing)
                ->default_value(false)
                ->implicit_value(true),
        "Set inprocessing in CaDiCal DRUP2ITP minimizer for interpolation")(
        "cadical_itp_minimizer_preprocessing",
        po::value<bool>(&gParams.cadical_itp_minimizer_preprocessing)
                ->default_value(false)
                ->implicit_value(true),
        "Set inprocessing in CaDiCal DRUP2ITP minimizer for interpolation")(
        "cadical_itp",
        po::value<bool>(&gParams.cadical_itp)
                ->default_value(false)
                ->implicit_value(true),
        "Use Cadical DRUP 2.0.0 for interpolation")(
      "glucose_itp",
      po::value<bool>(&gParams.glucose_itp)
          ->default_value(true)
          ->implicit_value(true),
      "Use Glucose for interpolation")(
    "certificate",
                po::value<string>(&gParams.certificate)
                        ->default_value("certificate.aig")
                        ->implicit_value("certificate.aig"),
                "Provide a file name for avy certificate")(
      "kstep,k", po::value<unsigned>(&gParams.kStep)->default_value(1),
      "Step size for BMC problems")("stick-error",
                                    po::value<bool>(&gParams.stick_error)
                                        ->default_value(false)
                                        ->implicit_value(true),
                                    "Stick error output")(
      "itp-simplify",
      po::value<bool>(&gParams.itp_simplify)->default_value(true),
      "Simplify the interpolant using synthesis")(
      "max-frame",
      po::value<unsigned>(&gParams.maxFrame)->default_value(100000),
      "Max BMC depth")(
      "gen-conf-limit",
      po::value<unsigned>(&gParams.genConfLimit)->default_value(0))(
      "sat-simp",
      po::value<bool>(&gParams.sat_simp)
          ->default_value(true)
          ->implicit_value(true),
      "Enable pre-processing for the non-interpolating SAT solver (if "
      "available)")(
      "itp-simp",
      po::value<bool>(&gParams.itp_simp)
          ->default_value(false)
          ->implicit_value(true),
      "Enable pre-processing during interpolation (if available)")(
      "muser-min-suffix",
      po::value<bool>(&gParams.muser_min_suffix)
          ->default_value(false)
          ->implicit_value(true),
      "Muser computes core starting from the last unrolling")(
      "muser-min-prefix",
      po::value<bool>(&gParams.muser_min_prefix)
          ->default_value(false)
          ->implicit_value(true),
      "Muser computes core starting from the first unrolling")(
      "muser-unser-mr",
      po::value<bool>(&gParams.muser_unset_mr_mode)
          ->default_value(true)
          ->implicit_value(true),
      "Disable model rotation in muser")(
      "proof-reorder",
      po::value<bool>(&gParams.proof_reorder)
          ->default_value(false)
          ->implicit_value(true),
      "Enable proof reordering for the interpolating SAT solver (if "
      "available)")("glucose-inc-mode",
                    po::value<bool>(&gParams.glucose_inc_mode)
                        ->default_value(false)
                        ->implicit_value(true),
                    "Enable Glucose incremental mode")(
      "cex", po::value<std::string>(&gParams.cexFileName)->default_value(""),
      "Location to output counter-example")("opt-bmc",
                                            po::value<bool>(&gParams.opt_bmc)
                                                ->default_value(true)
                                                ->implicit_value(true),
                                            "Enable optimized BMC")(
      "quip",
      po::value<bool>(&gParams.quip)
          ->default_value(false)
          ->implicit_value(true),
      "Try and push lemmas")("reverseSA",
                             po::value<bool>(&gParams.reverseSA)
                                 ->default_value(false)
                                 ->implicit_value(true),
                             "Reverse suffix assumption")(
      "mink",
      po::value<int>(&gParams.minK)->default_value(-1)->implicit_value(-1),
      "repeat k-inductive frame atleast minK times in the proof")(
      "commitAbs",
      po::value<bool>(&gParams.commitAbs)
          ->default_value(false)
          ->implicit_value(true),
      "Commit to an abstraction when computing min core")(
      "kthr",
      po::value<unsigned>(&gParams.kThr)->default_value(0)->implicit_value(0),
      "Stop searching for k-inductive frame once we reach a level N-kThr")(
      "suffixSA",
      po::value<bool>(&gParams.suffixSA)
          ->default_value(false)
          ->implicit_value(true),
      "apply abstraction only on suffix")(
      "extra-frames",
      po::value<unsigned>(&gParams.num_extra_frames)->default_value(100),
      "Extra frames to push past the last safe frame")(
      "kind-policy",
      po::value<unsigned>(&gParams.kind_policy)
          ->default_value(sel_algthms::top_down)
          ->implicit_value(sel_algthms::top_down),
      "which k-induction policy to use. 1) Minimize Suffix first then find "
      "Smallest k 2) Minimize Suffix first then find Largest k 3) Don't "
      "Minimize Suffix. Find Largest k");

  po::options_description hidden("Hidden options");
  hidden.add_options()("input-file", po::value<string>(), "input file");

  po::options_description cmdline;
  cmdline.add(generic).add(hidden);

  po::positional_options_description p;
  p.add("input-file", -1);

  try {
    po::variables_map vm;
    po::store(po::command_line_parser(argc, argv)
                  .options(cmdline)
                  .positional(p)
                  .run(),
              vm);
    po::notify(vm);

    if (vm.count("help")) {
      cout << generic << "\n";
      std::exit(1);
    }

    if (vm.count("print-params")) {
      cout << gParams << "\n";
      std::exit(1);
    }
    if (vm.count("version")) {
      cout << "Avy (" << AVY_BUILD_MODE << ")\n";
      if (!vm.count("input-file")) std::exit(1);
    }

    if (!vm.count("input-file")) {
      cout << "Error: No AIG file specified\n";
      std::exit(1);
    }

    if (vm.count("log")) {
      vector<string> logs = vm["log"].as<vector<string>>();
      for (vector<string>::iterator it = logs.begin(), end = logs.end();
           it != end; ++it)
        AvyEnableLog(it->c_str());
    }

    gParams.fName = vm["input-file"].as<string>();

    VERBOSE(2, vout() << gParams << "\n";);

    return gParams.fName;
  } catch (std::exception &e) {
    cout << "Error: " << e.what() << "\n";
    std::exit(1);
  }
}

int main(int argc, char *argv[]) {
  std::string fileName = parseCmdLine(argc, argv);
  int ret = 0;
  AVY_ASSERT(!gParams.lemmaAbs || !gParams.opt_bmc);
  if (gParams.avy) {
    AvyMain avy(fileName);
    ret = avy.run();
  } else {
    assert(false);
  }

  VERBOSE(1, Stats::PrintBrunch(outs()););
  return ret;
}
