#include "avy/Util/AvyDebug.h"
#include "avy/Util/AvyAssert.h"

#include <set>
#include <string>

#ifndef NAVYLOG
using namespace avy;

bool avy::AvyLogFlag = false;
std::set<std::string> avy::AvyLog;

void avy::AvyEnableLog(std::string x) {
  if (x.empty())
    return;
  AvyLogFlag = true;
  AvyLog.insert(x);
}

#else
#endif
