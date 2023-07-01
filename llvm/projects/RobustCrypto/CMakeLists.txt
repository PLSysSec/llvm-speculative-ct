set(LLVM_OPTIONAL_SOURCES
  AliasAnalysisVisitor.cpp
  AliasTaintCtx.cpp
  BaseContext.h
  GlobalVisitor.h
  ModObject.h
  RobustifyApp.cpp
  TaintAnalysisVisitor.cpp
  Utils.cpp
  VisitorCallback.h
  AliasAnalysisVisitor.h
  AliasTaintCtx.h
  CMakeLists.txt
  Instruction.def
  ModifyVisitor.h
  RobustifyLib.cpp
  TaintAnalysisVisitor.h
  Utils.h
  )

add_llvm_pass_plugin(RobustifyLibPass RobustifyLib.cpp
  Utils.h
  Utils.cpp
  )

add_llvm_pass_plugin(RobustifyAppPass RobustifyApp.cpp
  AliasAnalysisVisitor.cpp
  AliasTaintCtx.cpp
  BaseContext.h
  GlobalVisitor.h
  ModObject.h
  TaintAnalysisVisitor.cpp
  Utils.cpp
  VisitorCallback.h
  AliasAnalysisVisitor.h
  AliasTaintCtx.h
  CMakeLists.txt
  Instruction.def
  ModifyVisitor.h
  TaintAnalysisVisitor.h
  Utils.h
  )
