add_library(OmpKernelWrapper
  SHARED
  OmpKernelWrapper.cpp
)

install(TARGETS OmpKernelWrapper LIBRARY DESTINATION lib/llvm-support)
