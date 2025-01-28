#include <string>
#include <vector>

#include <avy/Util/AvyTribool.h>

#include "boost/noncopyable.hpp"
#include "boost/program_options.hpp"

#include "btor/metadata.h"

namespace po = boost::program_options;

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"
#include "AigUtils.h"
#include "AvyMain.h"

#include <cstdlib>
#include <iostream>
#include <time.h>

using namespace std;
using namespace abc;


using namespace boost;
using namespace std;
using namespace avy;

namespace ABC_NAMESPACE {
    extern Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}

static Aig_Man_t *loadAig(const std::string& fname) {
    Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame();

    VERBOSE(2, vout() << "\tReading AIG from '" << fname << "'\n";);
    std::string cmd = "read " + fname;
    Cmd_CommandExecute(pFrame, cmd.c_str());

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pFrame);

    return Abc_NtkToDar(pNtk, 0, 1);
}

static std::string gCnfFile;
static bool gDoBmc;

namespace avy {
    class AvyBtor : boost::noncopyable {
    private:
        std::string m_FName;
        MetaData m_md;


    public:
        explicit AvyBtor(const std::string& fname);

        avy::tribool run(unsigned uDepth);
    };

    AvyBtor::AvyBtor(const std::string& fname)
            : m_FName(fname), m_md(fname.c_str()) {
        VERBOSE(2, vout() << "Starting BTOR front-end\n");

    }

    tribool AvyBtor::run(unsigned uDepth) {
        Stats::set("Result", "UNKNOWN");
        VERBOSE(1, Stats::PrintBrunch(outs()););

        if (gParams.glucose) {

            // Collect selected metadata
            m_md.collect_ite_conditions();
            //m_md.print_btor_conditions();

            // Generate an AIG with metadata embedded into it
            Gia_Man_t *pAig = m_md.givemeAigWithMeta();

            // Generate a clean AIG
            Gia_Man_t * gia_mng_no_condStates = m_md.Gia_remove_condStates(pAig);
            //m_md.print_gia_conditions();

            // Generate assignments
            m_md.generate_assignments(pAig);
            //m_md.print_assignments();

            // Stop AIG
            Gia_ManStop(pAig);

            AigManPtr org_aigPtr = std::make_shared<Aig_Man_t>(*Gia_ManToAig(gia_mng_no_condStates, 0));
            AvyMain org_avy = AvyMain(org_aigPtr);
            printf("\norg ");
            int org_res = org_avy.run();
            printf("\nmine ");

            // prove per assignment
            int i=0;
            AvyTrace* trace;
            AvyMain* avy;
            AvyMain* old_avy;
            for (const auto& ass : m_md.assignments){
                i++;
                Gia_Man_t * pGia_ass = m_md.gia_per_assignment(gia_mng_no_condStates, ass);
                AigManPtr aigPtr = std::make_shared<Aig_Man_t>(*Gia_ManToAig(pGia_ass, 0));
                //AvyMain avy = AvyMain(aigPtr);
                old_avy = avy;
                if (i==1){
                    avy = new AvyMain(aigPtr);
                } else {
                    avy = new AvyMain(aigPtr, trace);
                    //delete old_avy;
                }
                //std::cout << "running with assignment " << i << " of " << m_md.assignments.size();
                //std::cout.flush();
                //for (auto const& [obj, val] : ass){
                //    std::cout << obj << ": " << val << "\t";
                //}
                if (i%180 == 0){
                    std::cout << std::endl;
                }
                int res = avy->run();
                trace = avy->getTrace();
                Gia_ManStop(pGia_ass);
                if (res != 0) {
                    //return res;
                    return res == org_res;
                }
            }
            //delete old_avy;
            Gia_ManStop(gia_mng_no_condStates);
            // return 1;
            return (0 == org_res);
        }

        VERBOSE(1, Stats::PrintBrunch(outs()););
        return 0;
    }

} // namespace avy

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
            po::value<bool>(&gParams.tr0)->default_value(false)->implicit_value(true),
            "Make only Tr0 be special (stutter or reset init)")(
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
                    "Set preprocessing in CaDiCal DRUP2ITP minimizer for interpolation")(
            "cadical_itp",
                    po::value<bool>(&gParams.cadical_itp)
                            ->default_value(false)
                            ->implicit_value(true),
                    "Use CaDiCal DRUP2ITP for interpolation")(
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
            "stick-error",
            po::value<bool>(&gParams.stick_error)
                    ->default_value(false)
                    ->implicit_value(true),
            "Stick error output")(
            "itp-simplify",
            po::value<bool>(&gParams.itp_simplify)->default_value(true),
            "Simplify the interpolant using synthesis")(
            "depth", po::value<unsigned>(&gParams.maxFrame)->default_value(1),
            "BMC depth")("dump-cnf", po::value<std::string>(&gCnfFile),
                         "File to dump CNF of the unrolling")(
            "bmc",
            po::value<bool>(&gDoBmc)->default_value(true)->implicit_value(true),
            "Do BMC")("sat-simp",
                      po::value<bool>(&gParams.sat_simp)
                              ->default_value(false)
                              ->implicit_value(true),
                      "Enable pre-processing for the non-interpolating SAT solver "
                      "(if available)")("glucose-inc-mode",
                                        po::value<bool>(&gParams.glucose_inc_mode)
                                                ->default_value(false)
                                                ->implicit_value(true),
                                        "Enable Glucose incremental mode")(
            "cex", po::value<std::string>(&gParams.cexFileName)->default_value(""),
            "Location to output counter-example")("opt-bmc",
                                                  po::value<bool>(&gParams.opt_bmc)
                                                          ->default_value(true)
                                                          ->implicit_value(true),
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
            for (auto&& it: logs)
                AvyEnableLog(it);
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
    AvyBtor btor_mc(fileName);

    tribool res = btor_mc.run(gParams.maxFrame);
    return res;
}
