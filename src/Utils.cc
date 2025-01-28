#include "avy/Util/Utils.h"

#include <cmath>

namespace avy {
unsigned getLuby(unsigned i) {
  if (i == 1)
    return 1;
  double k = log(static_cast<double>(i + 1)) / log(static_cast<double>(2));

  if (k == floor(k + 0.5))
    return static_cast<unsigned>(pow(2, k - 1));
  else {
    k = static_cast<unsigned>(floor(k));
    return getLuby(i - static_cast<unsigned>(pow(2, k)) + 1);
  }
}

} // namespace avy
