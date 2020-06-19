add_library(OmpHostPointerLegalizer
  SHARED
  OmpHostPointerLegalizer.cpp
)

install(TARGETS OmpHostPointerLegalizer LIBRARY DESTINATION lib/llvm-support)
