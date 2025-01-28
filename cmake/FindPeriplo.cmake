# Find Periplo

set(PERIPLO_ROOT "" CACHE PATH "Root of Periplo installation.")

find_path(PERIPLO_INCLUDE_DIR NAMES PeriploContext.h PATHS ${PERIPLO_ROOT}/include)
find_library(PERIPLO_LIBRARY NAMES periplolibrary PATHS ${PERIPLO_ROOT}/lib)


include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Periplo
  REQUIRED_VARS PERIPLO_LIBRARY PERIPLO_INCLUDE_DIR)

mark_as_advanced(PERIPLO_LIBRARY PERIPLO_INCLUDE_DIR)