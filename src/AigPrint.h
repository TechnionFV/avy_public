#ifndef _AIGPRINT_H_
#define _AIGPRINT_H_

/** C++ debug printing of AIG */

#include <iostream>

#include "aig/aig/aig.h"
#include "avy/abc/pdr/pdrInt.h"

namespace avy {
std::ostream &PrintAig(std::ostream &out, abc::Aig_Man_t *pMan,
                       abc::Aig_Obj_t *obj);
std::ostream &PrintAigMan(std::ostream &out, abc::Aig_Man_t *man);

std::ostream &PrintPdrSet(std::ostream &out, avy_abc_pdr::Pdr_Set_t *pCube);
std::ostream &PrintPdrSets(std::ostream &out, abc::Vec_Ptr_t &cubes);

inline std::ostream &operator<<(std::ostream &out, abc::Aig_Man_t &man) {
  PrintAigMan(out, &man);
  return out;
}

inline std::ostream &operator<<(std::ostream &out,
                                avy_abc_pdr::Pdr_Set_t &cube) {
  PrintPdrSet(out, &cube);
  return out;
}
} // namespace avy

#endif /* _AIGPRINT_H_ */
