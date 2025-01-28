#pragma once

namespace avy {

class tribool {
private:
  enum class eVal {
    UNDEF = 0,
    TRUE = 1,
    FALSE = 2
  };


  eVal m_Val;

public:
  tribool() : m_Val(eVal::UNDEF) {}
  tribool(eVal val) : m_Val(val) {}
  tribool(bool init) {
    m_Val = (init) ? eVal::TRUE : eVal::FALSE;
  }
  tribool(const tribool & other) : m_Val(other.m_Val) {}
  tribool & operator=(const tribool & other) {
    m_Val = other.m_Val;
    return *this;
  }
  tribool & operator=(bool other) {
    m_Val = (other) ? eVal::TRUE : eVal::FALSE;
    return *this;
  }

  bool undef() const { return m_Val == eVal::UNDEF; }

  operator bool() const { return m_Val == eVal::TRUE; }
  tribool operator!() const
  {
    tribool tmp (*this);
    if (!undef()) {
      tmp.m_Val = m_Val == eVal::TRUE ? eVal::FALSE : eVal::TRUE;
    }
    return tmp;
  }
};

}

