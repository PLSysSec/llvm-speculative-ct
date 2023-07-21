set(LLVM_OPTIONAL_SOURCES
  AliasAnalysisVisitor.cpp
  AliasTaintCtx.cpp
  RobustifyApp.cpp
  TaintAnalysisVisitor.cpp
  Utils.cpp
  CMakeLists.txt
  Instruction.def
  ModifyVisitor.cpp
  RobustifyLib.cpp
  )

add_llvm_pass_plugin(RobustifyLibPass RobustifyLib.cpp
  Utils.cpp
  )

add_llvm_pass_plugin(RobustifyAppPass RobustifyApp.cpp
  AliasAnalysisVisitor.cpp
  AliasTaintCtx.cpp
  TaintAnalysisVisitor.cpp
  Utils.cpp
  CMakeLists.txt
  Instruction.def
  ModifyVisitor.cpp
  Utils.cpp
  )
