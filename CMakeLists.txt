project(ClauseItpSeq)
cmake_minimum_required(VERSION 3.5.0)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

# Add path for custom modules
set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake"
  )

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)
add_definitions ("-std=c++17")

option(AVY_STATIC_EXE "Static executables." OFF)

set (CUSTOM_BOOST_ROOT "" CACHE PATH "Path to custom boost installation.")
if (CUSTOM_BOOST_ROOT)
  set (BOOST_ROOT ${CUSTOM_BOOST_ROOT})
  set (Boost_NO_SYSTEM_PATHS "ON")
endif()

set (Boost_USE_STATIC_LIBS ${AVY_STATIC_EXE})
find_package (Boost 1.46.1 REQUIRED program_options)
IF (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
endif ()

# prefer linking with static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

set(ZLIB_USE_STATIC_LIBS ${AVY_STATIC_EXE})
find_package(ZLIB REQUIRED)

# A workaround for zlib
if (AVY_STATIC_EXE)
   message (${ZLIB_LIBRARIES})
   string(REPLACE "libz.so" "libz.a" ZLIB_LIBRARIES ${ZLIB_LIBRARIES})
   message (${ZLIB_LIBRARIES})
endif()

# check for rt lib. Not needed on OSX.
find_library(RT_LIB NAMES rt)
if (NOT RT_LIB)
  set(RT_LIB "")
endif()
mark_as_advanced(RT_LIB)

find_package(Abc REQUIRED)
if (ABC_FOUND)
  include_directories(${ABC_INCLUDE_DIR})
  ## AG: hack to expand a list to space-separated string
  foreach (flag ${ABC_CXXFLAGS})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  endforeach()
  add_definitions (-DABC_NAMESPACE=${ABC_NAMESPACE})
else()
  set(ABC_LIBRARY "")
endif ()

find_package(Btor2Tools REQUIRED)
if (BTOR2TOOLS_FOUND)
  include_directories(${BTOR2TOOLS_INCLUDE_DIR})
  include_directories(${AIGER_INCLUDE_DIR})
  find_package(Boolector REQUIRED)
endif()

find_package(Minisat)
if (MINISAT_FOUND)
  include_directories(${MINISAT_INCLUDE_DIR})
else()
  set (MINISAT_LIBRARY "")
endif()
 
find_package(Glucose)
if (GLUCOSE_FOUND)
  include_directories(${GLUCOSE_INCLUDE_DIR})
else()
  set (GLUCOSE_LIBRARY "")
endif()

find_package(Muser2)
if (MUSER2_FOUND)
  include_directories(${MUSER2_INCLUDE_DIR})
else()
  set (MUSER2_LIBRARY "")
endif()

find_package(Cadical)
if (CADICAL_FOUND)
  include_directories(${CADICAL_INCLUDE_DIR})
else()
  set (CADICAL_LIBRARY "")
endif()

include_directories(
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/include
  )

add_subdirectory(src)
