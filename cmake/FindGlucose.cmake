# Find Glucose

set(GLUCOSE_ROOT "" CACHE PATH "Root of Glucose installation.")

if (DEFINED Glucose_SOURCE_DIR)
  include ("${Glucose_SOURCE_DIR}/cmake/PackageOptions.cmake")
else()
  find_path(GLUCOSE_INCLUDE_DIR NAMES glucose/core/Solver.h 
    PATHS ${GLUCOSE_ROOT}/include)
  find_library(GLUCOSE_LIBRARY  NAMES glucose  PATHS ${GLUCOSE_ROOT}/lib)
endif()

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Glucose
  REQUIRED_VARS GLUCOSE_LIBRARY GLUCOSE_INCLUDE_DIR)

mark_as_advanced(GLUCOSE_LIBRARY GLUCOSE_INCLUDE_DIR)