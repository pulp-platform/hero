ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Source files to include in test
CSRCS = $(wildcard *.c)

# As outlined in issue #91, the qsort algorithm performs incorrectly if
# compiled with -O3 (default) in Clang 9.0.0. Since we expect to upgrade LLVM
# to version 11 in the near future, we defer solving his issue until after the
# upgrade, if it still appears there. This check ensures that as soon as LLVM
# is upgraded this test will be compiled with the default optimization level
# -O3, and if the bug persists, it will trigger an error.
CLANGVERSION=$(shell clang -dumpversion)
ifeq "$(CLANGVERSION)" "9.0.0"
opt=2
endif

# Include common options and then the common build system
-include $(ROOT)/../include/common.mk
-include $(ROOT)/../../common/default.mk
