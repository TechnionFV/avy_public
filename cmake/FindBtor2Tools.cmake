# Find Btor

if (DEFINED btor2tools_SOURCE_DIR)
  set (BTOR2PARSER_LIBRARY btor2parser.LIB)
  set (BTOR2AIGER_LIBRARY btor2aiger.LIB)
  set (BTOR2TOOLS_INCLUDE_DIR ${btor2tools_SOURCE_DIR}/src)
  set (AIGER_INCLUDE_DIR ${btor2tools_BINARY_DIR}/deps/aiger)
else()
  message (STATUS "Compiling AVY with external Btor2Tools is not supported. Use extavy")
endif()


include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Btor2Tools
  REQUIRED_VARS BTOR2PARSER_LIBRARY BTOR2AIGER_LIBRARY BTOR2TOOLS_INCLUDE_DIR)

mark_as_advanced(BTOR2TOOLS_LIBRARY BTOR2AIGER_LIBRARY BTOR2TOOLS_INCLUDE_DIR)
