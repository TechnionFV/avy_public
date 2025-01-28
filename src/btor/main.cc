#include "metadata.h"

#include <string>
#include <stdio.h>

#include "aig/aig/aig.h"
#include "utils.h"
#include "aig/gia/gia.h"

#include "btor2aiger.h"

using namespace std;
using namespace abc;


int main(int argc, char* argv[]) {

    if (argc != 2) return -1;

    string btor2_path = argv[1];

    // Create the MetaData object and read the btor file
    MetaData m_md(btor2_path.c_str());

    // Collect selected metadata
    m_md.collect_ite_conditions();
    m_md.print_btor_conditions();

    // Generate an AIG with metadata embedded into it
    Gia_Man_t *pAig = m_md.givemeAigWithMeta();

    // Generate a clean AIG
    Gia_Man_t * gia_mng_no_condStates = m_md.Gia_remove_condStates(pAig);
    m_md.print_gia_conditions();

    // Generate assignments
    m_md.generate_assignments(pAig);
    m_md.print_assignments();

    // Stop AIG
    Gia_ManStop(pAig);

    // prove per assignment

    Gia_ManStop(gia_mng_no_condStates);
}
