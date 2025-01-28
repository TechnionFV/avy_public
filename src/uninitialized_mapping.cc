//
// Created by Yakir Vizel on 9/12/24.
//

#include <fstream>
#include <string>

#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"
#include "base/main/main.h"

using namespace abc;

int main(int argc, char** argv) {
    if (argc < 2) exit(2);
    Abc_Start();
    std::string fname(argv[1]);
    Abc_Frame_t *pAbc = Abc_FrameGetGlobalFrame();
    std::string cmd = "read " + fname;
    Cmd_CommandExecute(pAbc, cmd.c_str());

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    unsigned PIs = Abc_NtkPiNum(pNtk);

    std::string fout = "mapping.txt";
    if (argc == 3) fout = argv[2];
    std::ofstream output(fout);
    std::cout << "Generating mapping. Writing to " << fout << std::endl;
    // First, generate the default mapping for the existing inputs
    unsigned i = 0;
    Abc_Obj_t *pObj = nullptr;
    Abc_NtkForEachPi(pNtk, pObj, i) {
        output << "i" << i << " = " << 2*(i+1) << std::endl;
    }

    // Second, for every uninitialized latch, map the generated input to that latch
    unsigned count = 0;
    i = 0;
    Abc_NtkForEachLatch(pNtk, pObj, i) {
        if (Abc_LatchIsInitDc(pObj)) {
            output << "i" << PIs + (count++) << " = " << 2 * (PIs + 1 + i) << std::endl;
        }
    }

    output.close();

    Abc_Stop();

    return 1;
}