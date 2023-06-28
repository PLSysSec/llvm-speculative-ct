set(LLVM_OPTIONAL_SOURCES
  RobustifyLib.cpp
  RobustifyApp.cpp
  AliasAnalysisVisitor.h AliasAnalysisVisitor.cpp
  AliasTaintCtx.h AliasTaintCtx.cpp
  BaseContext.h
  GlobalVisitor.h
  ModifyVisitor.h
  TaintAnalysisVisitor.h TaintAnalysisVisitor.cpp
  VisitorCallback.h
  )

add_llvm_pass_plugin(RobustifyLibPass RobustifyLib.cpp
  Utils.h
  Utils.cpp
  )

add_llvm_pass_plugin(RobustifyAppPass RobustifyApp.cpp
  Utils.h
  Utils.cpp
  AliasAnalysisVisitor.h AliasAnalysisVisitor.cpp
  AliasTaintCtx.h AliasTaintCtx.cpp
  BaseContext.h
  GlobalVisitor.h
  ModifyVisitor.h
  TaintAnalysisVisitor.h TaintAnalysisVisitor.cpp
  VisitorCallback.h
  )
