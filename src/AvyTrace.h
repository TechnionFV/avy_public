#pragma once
#include <algorithm>
#include <iostream> //ostream for overloading the << operator
#include "avy/Util/Stats.h"
#include "avy/Util/AvyDebug.h"
#include "AvyTypes.h"
//TO DO
// static assert
// try different data types for m_db
namespace avy
{

/**
A lemma is a clause annotated with additional properties
such as the largest frame at which the lemma is active.
*/
class AvyLemma {
    /** an integer id of the lemma */
    unsigned m_id;

    /** largest frame at which the lemma is active */
    unsigned m_frame;
    /** whether a lemma is an inductive invariant */
    bool m_invar;
    /** whether the lemma is currently active in some frame */
    bool m_active;
    /** extra properties go here */

    Clause m_clause;

    /**
       Refinement after initial implementation:
       (a) use bit-fields to pack properties
       (b) use flexible array member to allocate m_clause
           (https://en.wikipedia.org/wiki/Flexible_array_member)
     */

public:
    //default constructor
  AvyLemma() : m_frame(0), m_invar(false), m_active(false), m_clause(200) {}
  // copy constructor
  // copies everything except the id
  AvyLemma(const AvyLemma &lemma)
      : m_frame(lemma.getFrame()), m_invar(lemma.isInv()), m_active(lemma.isActive()),
        m_clause(lemma.getLiterals()) {}

  /** methods to access fields */
  unsigned getId() const { return m_id; }
  void setId(unsigned id) { m_id = id; }
  bool isActive() const { return m_active; }
  void setActive(bool v) { m_active = v; }
  void setInv() { m_invar = true; }
  bool isInv() const { return m_invar; }
  const Clause &getLiterals() const { return m_clause; }
  unsigned getFrame() const { return m_frame; }
  void setFrame(unsigned f) { m_frame = f; }

  /** resets literals and frame */
  void reset(const Clause &c, unsigned frame) {
    m_clause.clear();
    m_clause = c;
    m_frame = frame;
    }

    friend std::ostream& operator<<(std::ostream& os,const AvyLemma & lemma)
    {
        for(lit l : lemma.getLiterals())
        {
            os<<" "<<l;
        }
        return os;
    }
};
/**
   Trace of Lemmas providing access and uniqueness to lemmas
 */
class AvyTrace {
    /// place holder for sort
    Clause m_sortClause;
    /// place holder for lemmas to be added to trace
    AvyLemma m_localLemma;
    /// the actual m_db. Not stored in any particular order
    std::vector<std::unique_ptr<AvyLemma>> m_db;
    /// id of lemmas
    unsigned m_counter;


    //ordering of lemmas
    //returns a<b
    struct LemmaLessThan
    {
        template <typename T, typename U>
        bool operator () (const T& a, const U& b) const {
            const Clause & clauseA = a->getLiterals();
            const Clause & clauseB = b->getLiterals();
            if(clauseA.size()<clauseB.size()) { return true; }
            if(clauseA.size()>clauseB.size()) { return false; }
            int count=0;
            for(auto l : clauseA)
            {
                if(l > clauseB.at(count))
                    return false;
                if(l < clauseB.at(count))
                    return  true;
                count++;
            }
            return false;
        }
    };

    ///Checks whether two lemmas are equal
    ///Two lemmas are equal if their clauses are equal
    struct LemmaEqual
    {
        template <typename T, typename U>
        bool operator () (const T & a, const U & b){
            const Clause & clauseA = a->getLiterals();
            const Clause & clauseB = b->getLiterals();
            if(clauseA.size()!=clauseB.size()) { return false; }
            int count=0;
            for(auto l : clauseA)
            {
                if(l!=clauseB.at(count))
                    return false;
                count++;
            }
            return true;
        }
    }lemmasEqual;
     /*
      * Add a lemma to the trace.
      * If a lemma with the same clause already exists,
      * update its frame to the maximum of
      * old and new frames
      * Fetch the first pos not less than lemma
      * if *pos is equal to the lemma, update frame
      * else add lemma right before pos by shifting m_db[pos:end]
      */
    AvyLemma & insert(const AvyLemma &lemma)
    {
        AVY_MEASURE_FN;
        std::vector<std::unique_ptr<AvyLemma>>::iterator pos = std::lower_bound(m_db.begin(),m_db.end(),&lemma,LemmaLessThan());
        if(pos==m_db.end())
        {
            ScoppedStats _s_("TraceAppending");
            LOG("trace", logs()<<"ADDING LEMMA : "<<lemma<<std::endl;);
            m_counter++;
            std::unique_ptr<AvyLemma> newLemma = std::unique_ptr<AvyLemma>(new AvyLemma(lemma));
            newLemma->setId(m_counter);
            m_db.push_back(std::move(newLemma));
            Stats::uset("TraceLemmas",m_counter);
            return *m_db.back();
        }
        if(lemmasEqual(&lemma,*pos))
        {
            unsigned frame = lemma.getFrame();
            if(frame > (*pos)->getFrame())
                (*pos)->setFrame(frame);
            return *(*pos);
        }
        else
        {
            //copies each pointer to the right of pos
            //very expensive
            ScoppedStats _s_("TraceShiftingPointers");
            LOG("trace", logs() << "ADDING LEMMA : " << lemma << std::endl;);
            m_counter++;
            std::unique_ptr<AvyLemma> newLemma = std::unique_ptr<AvyLemma>(new AvyLemma(lemma));
            newLemma->setId(m_counter);
            Stats::uset("TraceLemmas",m_counter);
            return *(*m_db.insert(pos,std::move(newLemma)));
        }
    }
public :
    AvyTrace():m_sortClause(Clause(200)),m_counter(0)
    {
    }

    /** Create a lemma from a given clause and frame */
    AvyLemma &mkLemma(const Clause &cls, unsigned frame,bool fcompl=false)
    {
        m_sortClause.clear();
        m_sortClause=cls;
        std::sort(m_sortClause.begin(),m_sortClause.end());
        if(fcompl)
            for(auto & l : m_sortClause)
            {
                l=lit_neg(l);
            }
        //The lifetime of these references are determined by the m_db
        //so the references returned will not be invalid at any point
        //this implementation does not support deleting things from the m_db
        m_localLemma.reset(m_sortClause,frame);
        return insert(m_localLemma);
    }
    /*
     * Constructs a lemma of literals from start to end
     */
    template <typename Iterator>
    AvyLemma &mkLemma(Iterator start, Iterator end, unsigned frame=-1,bool fcompl=false)
    {
        m_sortClause.clear();
        AVY_ASSERT(start!=end);
        std::copy(start,end,std::back_inserter(m_sortClause));
        std::sort(m_sortClause.begin(),m_sortClause.end());
        if(fcompl)
        {
            for(auto & l : m_sortClause)
            {
                l=lit_neg(l);
            }
        }
        m_localLemma.reset(m_sortClause,frame);
        return insert(m_localLemma);
    }
    /**
     * Fetches all lemmas in frame nFrame
     */
    void getLemmasAtFrame(unsigned nFrame, Lemmas & lemmasAtFrame)
    {
        AVY_MEASURE_FN;
        lemmasAtFrame.clear();
        for (const std::unique_ptr<AvyLemma> & lptr : m_db) {
                if(lptr->getFrame()>=nFrame)
                {
                    lemmasAtFrame.push_back(lptr.get());
                }
        }
    }
};
}//namespace avy
