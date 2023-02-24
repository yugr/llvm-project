add_llvm_library(FindInternalCandidates MODULE FindInternalCandidates.cpp PLUGIN_TOOL clang)

if(WIN32 OR CYGWIN)
  set(LLVM_LINK_COMPONENTS
    Support
  )
  clang_target_link_libraries(FindInternalCandidates PRIVATE
    clangAST
    clangBasic
    clangFrontend
    clangLex
    )
endif()
