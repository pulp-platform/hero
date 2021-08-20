ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Source files to include in test
CSRCS = $(wildcard *.c)

# As outlined in issue #91, the qsort algorithm performs incorrectly if
# compiled with -O3 (default) in Clang 9.0.0. Since we expect to upgrade LLVM
# to version 11 in the near future, we defer solving his issue until after the
# upgrade, if it still appears there. This check ensures that as soon as LLVM
# is upgraded this test will be compiled with the default optimization level
# -O3, and if the bug persists, it will trigger an error.
# *** UPDATE: This error persists in LLVM 12.0.1 -- there must be something very
#             wrong with LLVM or how the algorithm is implemented. Issue #91
#             states that qsort hangs with -O3, which was the case under LLVM 9.
#             In LLVM 12 we instead get:
#             	Error: Branch decision is X in module pulp_tb.dut.
#             				 gen_clusters[0].gen_cluster_sync.i_cluster.i_ooc.i_bound.
#             				 CORE[0].core_region_i.RISCV_CORE.id_stage_i!
#             which seems to indicate that this is actually a problem in the hW?
CLANGVERSION=$(shell clang -dumpversion)
ifeq "$(CLANGVERSION)" "12.0.1"
opt=2
endif

# Include common options and then the common build system
-include $(ROOT)/../include/common.mk
-include $(ROOT)/../../common/default.mk
