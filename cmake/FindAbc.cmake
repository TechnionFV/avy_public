# Find Abc
include(CMakeParseArguments)
include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

if(READLINE_FOUND MATCHES TRUE)
  addprefix(ABC_READLINE_INCLUDES_FLAGS "-I" ${READLINE_INCLUDE})
  string(REPLACE ";" " " ABC_READLINE_INCLUDES_FLAGS "${ABC_READLINE_INCLUDES_FLAGS}")
  list(APPEND ABC_READLINE_FLAGS "ABC_READLINE_INCLUDES=${ABC_READLINE_INCLUDES_FLAGS}")

  string(REPLACE ";" " " ABC_READLINE_LIBRARIES_FLAGS "${READLINE_LIBRARIES}")
  list(APPEND ABC_READLINE_FLAGS "ABC_READLINE_LIBRARIES=${ABC_READLINE_LIBRARIES_FLAGS}")
elseif(READLINE_FOUND MATCHES FALSE)
  list(APPEND ABC_READLINE_FLAGS "ABC_USE_NO_READLINE=1")
endif()

if(ABC_USE_NAMESPACE)
  set(ABC_USE_NAMESPACE_FLAGS "ABC_USE_NAMESPACE=${ABC_USE_NAMESPACE}")
endif()

if( APPLE )
  set(make_env ${CMAKE_COMMAND} -E env SDKROOT=${CMAKE_OSX_SYSROOT})
endif()

# run make to extract compiler options, linker options and list of source files
execute_process(
  COMMAND
  ${make_env}
  make
  ${ABC_READLINE_FLAGS}
  ${ABC_USE_NAMESPACE_FLAGS}
  ARCHFLAGS_EXE=${abc_BINARY_DIR}/abc_arch_flags_program.exe
  ABC_MAKE_NO_DEPS=1
  CC=${CMAKE_C_COMPILER}
  CXX=${CMAKE_CXX_COMPILER}
  LD=${CMAKE_CXX_COMPILER}
  cmake_info
  WORKING_DIRECTORY ${abc_SOURCE_DIR}
  OUTPUT_VARIABLE MAKE_OUTPUT
)

# extract options from make output
function(extract_var SEPARATOR DEST_VARIABLE MAKE_OUTPUT)
  string(REGEX MATCH "${SEPARATOR} .* ${SEPARATOR}" TMP "${MAKE_OUTPUT}")
  string(REGEX REPLACE "${SEPARATOR} (.*) ${SEPARATOR}" "\\1" TMP "${TMP}")

  separate_arguments(TMP)

  set(${DEST_VARIABLE} ${TMP} PARENT_SCOPE)
endfunction()

extract_var(SEPARATOR_SRC ABC_SRC ${MAKE_OUTPUT})
extract_var(SEPARATOR_LIBS ABC_LIBS ${MAKE_OUTPUT})
extract_var(SEPARATOR_CFLAGS ABC_CFLAGS ${MAKE_OUTPUT})
extract_var(SEPARATOR_CXXFLAGS ABC_CXXFLAGS ${MAKE_OUTPUT})


# remove `-x c++` that is added by Abc
list(REMOVE_ITEM ABC_CXXFLAGS "-x")
list(REMOVE_ITEM ABC_CXXFLAGS "c++")

set(ABC_NAMESPACE "abc" CACHE STRING "Abc namespace to use")

if (DEFINED abc_SOURCE_DIR)
  set(ABC_LIBRARY libabc)
  set(ABC_INCLUDE_DIR ${abc_SOURCE_DIR}/src)
else()
    message (STATUS "Compiling AVY with external ABC is not supported. Use extavy")
endif()


include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Abc
  REQUIRED_VARS ABC_LIBRARY ABC_INCLUDE_DIR ABC_CXXFLAGS ABC_CFLAGS)

mark_as_advanced(ABC_LIBRARY ABC_INCLUDE_DIR ABC_CFLAGS ABC_CXXFLAGS)
