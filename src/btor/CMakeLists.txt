add_library (BtorAnalyzer.LIB STATIC metadata.cc)

target_link_libraries (BtorAnalyzer.LIB
        ${BTOR2AIGER_LIBRARY})

add_executable(btor-analyzer main.cc)
target_link_libraries(btor-analyzer BtorAnalyzer.LIB glucose.LIB AvyDebug ${ABC_LIBRARY})