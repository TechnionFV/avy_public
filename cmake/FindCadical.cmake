# Find Cadical

set(CADICAL_ROOT "" CACHE PATH "Root of Cadical installation.")

if (DEFINED Cadical_SOURCE_DIR)
    include("${Cadical_SOURCE_DIR}/cmake/PackageOptions.cmake")
else()
    find_path(CADICAL_INCLUDE_DIR NAMES cadical.hpp PATHS ${CADICAL_ROOT}/src)
    find_library(CADICAL_LIBRARY  NAMES cadical.LIB  PATHS ${CADICAL_ROOT}/src)
endif()

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Cadical
        REQUIRED_VARS CADICAL_LIBRARY CADICAL_INCLUDE_DIR)

mark_as_advanced(CADICAL_LIBRARY CADICAL_INCLUDE_DIR)
