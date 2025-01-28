#pragma once

#include <fstream>
#include <string>
#include <vector>

#include "boost/noncopyable.hpp"
#include "boost/scoped_ptr.hpp"
#include "boost/dynamic_bitset.hpp"

#include "aig/saig/saig.h"

#include "AvyTypes.h" //IntVector

namespace avy {
    template<typename Sat> class Unroller;
    class SafetyVC2;
    class tribool;

    class AvyBmc2 : boost::noncopyable {
    private:
        std::string m_FName;
        bool m_doBmc;
        bool m_returnAfterUnsat;
        AigManPtr m_Aig;

        std::string m_CnfFile;

        bool m_bRes;

        std::vector<bool> m_lastFrame;

        unsigned m_lastUnsatFrame;

        std::vector<std::vector<std::pair<int,int>>> *m_abs_lits;

        bool m_abstractionUsed;

        std::vector<int> m_abstraction;

        unsigned m_realInputs;

        bool m_bUseAbs;

    public:
        AvyBmc2(std::string fname, bool doBmc);
        AvyBmc2(
            abc::Aig_Man_t *pAig,
            bool cadical,
            bool retAfterUnsat,
            bool useAbs,
            int realInputs,
            std::vector<std::vector<std::pair<int,int>>> *abs_lits);

        ~AvyBmc2();

        avy::tribool run(unsigned uDepth, unsigned uStart, std::vector<boost::dynamic_bitset<>> *inputVals = nullptr);
        
        template<typename Sat>
        avy::tribool solve(SafetyVC2 &vc, 
            Sat &solver, 
            Unroller<Sat> &unroller,
            unsigned uDepth, 
            unsigned uStart, 
            std::vector<boost::dynamic_bitset<>> *inputVals);

        template<typename Sat>
        avy::tribool bmc(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                         unsigned uDepth);
        template<typename Sat>
        avy::tribool cegar_bmc(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                         unsigned uDepth);

        template<typename Sat>
        void printCex(Sat &s, Unroller<Sat> &unroller);

        template<typename Sat>
        void printCexBv(Sat &s, Unroller<Sat> &unroller);

        void setCnfFile(std::string &cnf) { m_CnfFile = cnf; }

        template<typename Sat>
        void getInputVals(Sat &s, Unroller<Sat> &unroller, std::vector<abc::lit> &vals);

        template<typename Sat>
        void unrollTo(SafetyVC2 &vc, Sat &solver, Unroller<Sat> &unroller,
                      unsigned uDepth);
        template<typename Sat>
        void generateHints(Unroller<Sat> &unroller, std::vector<boost::dynamic_bitset<>> & inputVals,
                           std::vector<abc::lit> &vals);

        unsigned getLastUnsatFrame() const { return m_lastUnsatFrame; }

    private:
        template <typename Sat>
        void prepareAbstraction(Unroller<Sat> &unroller, unsigned uDepth);

        template <typename Sat>
        bool refineAbstraction(Sat &sat, Unroller<Sat> &unroller);
    };
}