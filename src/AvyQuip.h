/**
 * Implementation of Quip algorithm for Avy
 */
#pragma once

#include "AvyMain.h"
#include "AvyTypes.h" //defines IntVector
#include "AvyUnsatCore.h"
namespace avy {
  class AvyQuip {
    AvyMain &m;
    std::vector<boost::dynamic_bitset<>> m_ReachableStates;

    template <typename Sat>
    void extractReachableState(Sat &s, Unroller<Sat> &unroller);

  public:
    AvyQuip(AvyMain &m) : m(m) {}
    template <typename Sat>
    tribool operator()(unsigned nFrame, Sat &solver, Muser2 &muser,
                       Unroller<Sat> &unroller,
                       UnsatCoreComputer<Sat> &unsatCoreComputer);
  };
}
