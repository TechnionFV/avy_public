add_library (ClauseItpSeq STATIC 
  Utils.cc Global.cc SafetyVC.cc SafetyVC2.cc Stats.cc SafetyAigVC.cc ItpValidator.cc ItpCadical.cc AvyCertificate.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AigUtils.cc CnfUtils.cc ItpMinisat.cc ItpGlucose.cc ItpCadical)
add_library (AvyDebug AvyDebug.cc)
add_library(AvyMc.LIB AvyMain.cc AvyQuip.cc)
add_library(AvyBmc.LIB AvyBmc2.cc)

# A workaround for zlib - add explicitly here
set (EXT_LIBRARIES ${ABC_LIBRARY} ${MINISAT_LIBRARY} ${GLUCOSE_LIBRARY} ${MUSER2_LIBRARY} ${CADICAL_LIBRARY})

add_executable (avy main.cc)
target_link_libraries (avy
  AvyMc.LIB
  ClauseItpSeq 
  AbcCpp
  AvyDebug
  pdr.LIB
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread
  ${RT_LIB})

add_executable (avybmc AvyBmc.cc)
target_link_libraries (avybmc
  ClauseItpSeq
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread ${ZLIB_LIBRARIES}
  ${RT_LIB})

target_link_libraries(AvyBmc.LIB
  ClauseItpSeq
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread ${ZLIB_LIBRARIES}
  ${RT_LIB})

add_executable (avybmc2 AvyBmc2Main.cc)
target_link_libraries (avybmc2
        AvyBmc.LIB)

add_executable(abcpdr AbcPdr.cc)
target_link_libraries (abcpdr
  ClauseItpSeq
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread ${ZLIB_LIBRARIES}
  ${RT_LIB})

add_executable(avypdr AvyPdr.cc)
target_link_libraries (avypdr
  ClauseItpSeq
  AbcCpp
  AvyDebug
  pdr.LIB
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread ${ZLIB_LIBRARIES}
  ${RT_LIB})

add_executable(avybtor AvyBtor.cc)
target_link_libraries (avybtor
  AvyMc.LIB
  ClauseItpSeq
  AbcCpp
  AvyDebug
  pdr.LIB
  BtorAnalyzer.LIB
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread ${ZLIB_LIBRARIES}
  ${RT_LIB})

add_executable(unintitialized_mapping uninitialized_mapping.cc)
target_link_libraries(unintitialized_mapping ${ABC_LIBRARY})

if (AVY_STATIC_EXE)
    set (CMAKE_EXE_LINKER_FLAGS "-static -static-libgcc -static-libstdc++")
    set_target_properties (avy PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avy PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (avybmc PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avybmc PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (AvyMc.LIB PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (AvyMc.LIB PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (AvyBmc.LIB PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (AvyBmc.LIB PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (avybmc2 PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avybmc2 PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (abcpdr PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (abcpdr PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (avypdr PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avypdr PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

include_directories(${CMAKE_CURRENT_BINARY_DIR})
set(AVY_BUILD_MODE ${CMAKE_BUILD_TYPE})
configure_file (BuildVariables.inc.in BuildVariables.inc @ONLY)

add_subdirectory(abc/pdr)
add_subdirectory(btor)
