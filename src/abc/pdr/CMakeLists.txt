add_definitions(-DABC_LIB=1)

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)

add_library (pdr.LIB STATIC
  pdrCnf.cc
  pdrCore.cc
  pdrInv.cc
  pdrMan.cc
  pdrSat.cc
  pdrTsim.cc
  pdrUtil.cc)

