#ifndef _AVYMAIN_H_
#define _AVYMAIN_H_

#include "AigUtils.h"
#include "Glucose.h"
#include "Minisat.h"
#include "Pdr.h"
#include "SafetyVC2.h"
#include "Unroller.h"
#include "avy/Util/AvyTribool.h"
#include "boost/dynamic_bitset.hpp"
#include <string>

#include "boost/noncopyable.hpp"

#include "AvyTypes.h" //IntVector
#include "AvyUnsatCore.h"
#include "ItpGlucose.h"
#include "ItpMinisat.h"
#include "ItpCadical.h"
#include "Muser2.h"

namespace avy {
class AvyMain : boost::noncopyable {
  std::string m_fName;
  AigManPtr m_Aig;

  AvyTrace* m_TraceMan;
  /** reference to the current VC */
  SafetyVC2 *m_Vc;

  Pdr *m_pPdr;
  unsigned m_lemmaLevel;

  boost::dynamic_bitset<> m_Core;

  unsigned m_LastCoreSize;

  template <typename Sat>
  avy::tribool
  solveWithCore(Sat &sat, Muser2 &muser, Unroller<Sat> &unroller,
                unsigned nFrame, AigManPtr pBad,
                UnsatCoreComputer<Sat> *unsatCoreComputer = nullptr);

public:
  AvyMain(std::string fname);
  AvyMain(AigManPtr pAig);
  AvyMain(AigManPtr pAig, AvyTrace* Trace); // TODO implement

  virtual ~AvyMain();

  Pdr* getPdr() {return m_pPdr;}
  AigManPtr getAig() {return m_Aig;}
  SafetyVC2* getVc() {return m_Vc;}
  AvyTrace* getTrace() {return m_TraceMan;}
  unsigned getLastCoreSize() {return m_LastCoreSize;}
  int run();
  template <typename Sat>
  int run(Sat &solver, Muser2 &muser, Unroller<Sat> &unroller);

  /// do BMC check up to depth nFrame
  template <typename Sat>
  tribool doBmc(unsigned nFrame, Sat &solver, Muser2 &muser,
                       Unroller<Sat> &unroller, AigManPtr pBad = NULL,
                       UnsatCoreComputer<Sat> *unsatCoreComputer = nullptr);
  /// convert interpolant into PDR trace
  tribool doPdrTrace(AigManPtr itp, bool dropLast = false);
  /// strengthen VC with current Pdr trace
  void doStrengthenVC();
  template <typename Sat>
  tribool doQuip(unsigned nFrame, Sat &solver, Muser2 &muser,
                 Unroller<Sat> &unroller,
                 UnsatCoreComputer<Sat> &unsatCoreComputer);

  bool validateItp(AigManPtr itp, bool propagate = false);

  ///adds pre-condition clauses to a single frame in vc
  void addPreCond(SafetyVC2& vc,int nFrame);

  template <typename Sat> void printCex(Sat &s, Unroller<Sat> &unroller);

  bool findItpConstraints(AigManPtr &itp,
                          std::vector<IntVector> &equivFrames,
                          AigManPtr pBad);

  void printInvCert(const std::string &);
};
} // namespace avy

#endif /* _AVYMAIN_H_ */
