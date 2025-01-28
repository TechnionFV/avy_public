#pragma once

#include "aig/aig/aig.h"
#include "sat/bsat/satSolver.h"
#include <memory>
#include <vector>

namespace avy {
typedef std::vector<abc::lit> Clause;
typedef std::vector<Clause> Clauses;
class AvyLemma; // forward declration
typedef std::vector<AvyLemma *> Lemmas;
typedef std::shared_ptr<abc::Aig_Man_t> AigManPtr;
typedef std::vector<int> IntVector;
enum sel_algthms { top_down = 1, bot_up = 2 };
} // namespace avy
