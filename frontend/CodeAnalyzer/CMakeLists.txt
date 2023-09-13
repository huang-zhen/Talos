# If we don't need RTTI or EH, there's no reason to export anything
# from the hello plugin.
if( NOT LLVM_REQUIRES_RTTI )
  if( NOT LLVM_REQUIRES_EH )
    set(LLVM_EXPORTED_SYMBOL_FILE ${CMAKE_CURRENT_SOURCE_DIR}/Analyzer.exports)
  endif()
endif()

if(WIN32 OR CYGWIN)
  set(LLVM_LINK_COMPONENTS Core Support)
endif()

add_llvm_loadable_module( LLVMAnalyzer
  Analyzer.cpp
  ipc_lock.cpp

  DEPENDS
  intrinsics_gen
  )

target_link_libraries( LLVMAnalyzer /home/james/code/llvm-3.8.0.src/lib/Transforms/CodeAnalyzer/dataflow/libdataflow.a rt
)
