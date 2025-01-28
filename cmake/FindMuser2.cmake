# Find Muser2

set(MUSER2_ROOT "" CACHE PATH "Root of Muser2 installation.")

if (DEFINED Muser2_SOURCE_DIR)
    include("${Muser2_SOURCE_DIR}/cmake/PackageOptions.cmake")
else()
    find_path(MUSER2_INCLUDE_DIR NAMES muser2_api.hh PATHS ${MUSER2_ROOT}/src)
    find_library(MUSER2_LIBRARY  NAMES muser2_api  PATHS ${MUSER2_ROOT}/src/api)
endif()

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Muser2
        REQUIRED_VARS MUSER2_LIBRARY MUSER2_INCLUDE_DIR)

mark_as_advanced(MUSER2_LIBRARY MUSER2_INCLUDE_DIR)