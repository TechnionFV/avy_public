#include <fstream>
#include <string>
#include <vector>

#include "AvyBmc2.h"

#include <avy/Util/AvyTribool.h>

#include "boost/noncopyable.hpp"
#include "boost/program_options.hpp"
#include "boost/scoped_ptr.hpp"
namespace po = boost::program_options;

#include "AigUtils.h"
#include "Glucose.h"
#include "Minisat.h"
#include "ItpGlucose.h"

#include "AigPrint.h"
#include "SafetyVC2.h"
#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"
#include "aig/saig/saig.h"

#include "Unroller.h"
#include "simp/SimpSolver.h"
#include "AvyTypes.h" //IntVector

using namespace boost;
using namespace std;
using namespace avy;
using namespace avy::abc;

static std::string gCnfFile;
static bool gDoBmc;
static bool gBvMode;
static unsigned gStart;

static std::string parseCmdLine(int argc, char **argv) {
  po::options_description generic("Options");
  generic.add_options()("help", "print help message")(
      "print-params", "print current parameters")(
      "log,L", po::value<std::vector<std::string>>(), "log levels to enable")(
      "verbose,v", po::value<unsigned>(&gParams.verbosity)->default_value(0),
      "Verbosity level: 0 means silent")(
      "stutter,s",
      po::value<bool>(&gParams.stutter)
          ->default_value(false)
          ->implicit_value(true),
      "Stutter circuit instead of reseting to the initial state")(
      "tr0",
      po::value<bool>(&gParams.tr0)->default_value(true)->implicit_value(true),
      "Make only Tr0 be special (stutter or reset init)")(
      "coi",
      po::value<bool>(&gParams.coi)->default_value(true)->implicit_value(true),
      "add Tr logic based on COI")(
          "incr",
          po::value<bool>(&gParams.incr)
                  ->default_value(false)
                  ->implicit_value(true),
          "load clauses to solver incrementally")(
      "sat1",
      po::value<bool>(&gParams.sat1)
          ->default_value(false)
          ->implicit_value(true),
      "Always use satSolver (do not use satSolver2)")(
      "minisat",
      po::value<bool>(&gParams.minisat)
          ->default_value(true)
          ->implicit_value(true),
      "Use Minisat 2.2.0 for abstraction")(
      "glucose",
        po::value<bool>(&gParams.glucose)
        ->default_value(false)
        ->implicit_value(true),
        "Use Glucose for abstraction")(
      "cadical",
        po::value<bool>(&gParams.cadical)
        ->default_value(false)
        ->implicit_value(true),
        "Use CaDiCaL for abstraction")(
      "stick-error",
      po::value<bool>(&gParams.stick_error)
          ->default_value(false)
          ->implicit_value(true),
      "Stick error output")(
      "depth", po::value<unsigned>(&gParams.maxFrame)->default_value(1),
      "BMC depth")(
      "start", po::value<unsigned>(&gStart)->default_value(0),
      "BMC depth")(
      "dump-cnf", po::value<std::string>(&gCnfFile),
                   "File to dump CNF of the unrolling")(
      "bmc",
          po::value<bool>(&gDoBmc)->default_value(true)->implicit_value(true),
          "Do BMC")(
      "bmc_inc_ass",
          po::value<bool>(&gParams.bmc_incremental_assignment)->default_value(false)->implicit_value(true),
          "Construct assignment incrementally")(
          "bv",
          po::value<bool>(&gBvMode)->default_value(false)->implicit_value(true),
          "SMT Solver mode")(
      "sat-simp",
               po::value<bool>(&gParams.sat_simp)
                    ->default_value(false)
                    ->implicit_value(true),
         "Enable pre-processing for the non-interpolating SAT solver (if available)")(
      "glucose-inc-mode",
               po::value<bool>(&gParams.glucose_inc_mode)
                                      ->default_value(false)
                                      ->implicit_value(true),
                                  "Enable Glucose incremental mode")(
      "cex", po::value<std::string>(&gParams.cexFileName)->default_value(""),
      "Location to output counter-example")(
      "opt-bmc",
                   po::value<bool>(&gParams.opt_bmc)->default_value(true)->implicit_value(true),
                        "Enable optimized BMC");

  po::options_description hidden("Hidden options");
  hidden.add_options()("input-file", po::value<std::string>(), "input file");

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
      outs() << generic << "\n";
      std::exit(1);
    }

    if (vm.count("print-params")) {
      outs() << gParams << "\n";
      std::exit(1);
    }

    if (!vm.count("input-file")) {
      outs() << "Error: No AIG file specified\n";
      std::exit(1);
    }

    if (vm.count("log")) {
      using namespace std;
      vector<string> logs = vm["log"].as<vector<string>>();
      for (vector<string>::iterator it = logs.begin(), end = logs.end();
           it != end; ++it)
        AvyEnableLog(it->c_str());
    }

    gParams.fName = vm["input-file"].as<std::string>();

    VERBOSE(2, vout() << gParams << "\n";);

    return gParams.fName;
  } catch (std::exception &e) {
    outs() << "Error: " << e.what() << "\n";
    std::exit(1);
  }
}

int main(int argc, char **argv) {
  std::string fileName = parseCmdLine(argc, argv);
  AvyBmc2 bmc(fileName, gDoBmc);
  bmc.setCnfFile(gCnfFile);

  tribool res = bmc.run(gParams.maxFrame, gStart);

  Abc_Stop();

  if (res)
    return 1;
  else if (!res)
    return 0;
  else
    return 2;
}
