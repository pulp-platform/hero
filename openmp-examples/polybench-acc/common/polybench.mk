PBMK_ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

ifeq ($(threads),)
	threads = 8
endif

PBFLAGS = -DPOLYBENCH_USE_SCALAR_LB -DPOLYBENCH_TIME -DPOLYBENCH_CYCLE_ACCURATE_TIMER -DNUM_TEAMS=1 -DNUM_THREADS=8 -DPOLYBENCH_DUMP_ARRAYS

INCPATHS = -I$(PBMK_ROOT)/../common
LIBPATHS = -L$(PBMK_ROOT)/../common
LDFLAGS_PULP = $(PBMK_ROOT)/../common/libpolybench-pulp.a
LDFLAGS = $(PBMK_ROOT)/../common/libpolybench-host.a
CFLAGS_COMMON += $(PBFLAGS)

DEPS += polybench

$(PBMK_ROOT)/libpolybench-host.a: $(PBMK_ROOT)/polybench.c
	${HERO_TOOLCHAIN_HOST_TARGET}-gcc -O3 $(PBFLAGS) -fPIC -c $(PBMK_ROOT)/polybench.c -o $(PBMK_ROOT)/polybench.o
	${HERO_TOOLCHAIN_HOST_TARGET}-ar rcs $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/polybench.o

$(PBMK_ROOT)/libpolybench-pulp.a: $(PBMK_ROOT)/polybench.c
	riscv32-hero-unknown-elf-gcc -O3 $(PBFLAGS) -fPIC -DPULP -c $(PBMK_ROOT)/polybench.c -o $(PBMK_ROOT)/polybench.o
	riscv32-hero-unknown-elf-ar rcs $(PBMK_ROOT)/libpolybench-pulp.a $(PBMK_ROOT)/polybench.o

polybench-clean:
	rm -rf $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/libpolybench-pulp.a

polybench: $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/libpolybench-pulp.a
