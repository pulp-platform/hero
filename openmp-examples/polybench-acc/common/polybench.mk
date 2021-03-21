PBMK_ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

ifeq ($(threads),)
	threads = 8
endif
ifeq ($(mem),)
	mem = 2
endif
ifeq ($(dma),)
  dma = n
endif

PBFLAGS = -DPOLYBENCH_USE_SCALAR_LB -DNUM_TEAMS=1 -DNUM_THREADS=$(threads) -DPOLYBENCH_HERO_MEM_LEVEL=$(mem) -I$(HERO_PULP_INC_DIR)

ifdef HERCULES_INSTALL
	export HERCULES_DEFAULT_NUM_THREADS=$(threads)
endif

ifneq ($(dma),n)
	PBFLAGS += -DPOLYBENCH_DMA
ifneq ($(dma),optnone)
	PBFLAGS += -DDMALIB_DEVICE_AS
else
	AS_ANNOTATE_ARGS += "-hero-disable-as-assign-opt"
endif
endif

ifneq ($(dump),n)
	PBFLAGS += -DPOLYBENCH_DUMP_ARRAYS
endif

ifeq ($(offload-tgt),copy)
	PBFLAGS += -DTARGET_DEVICE=BIGPULP_MEMCPY
endif

INCPATHS += -I$(PBMK_ROOT)/../common
LIBPATHS += -L$(PBMK_ROOT)/../common
CFLAGS_COMMON += $(PBFLAGS)
LDFLAGS_PULP += -lpolybench-pulp
LDFLAGS += -lpolybench-host

DEPS += polybench

PBFLAGS_PULP = -DPOLYBENCH_NO_FLUSH_CACHE -DPOLYBENCH_CYCLE_ACCURATE_TIMER
CFLAGS_DMATRANSFER = -I$(PBMK_ROOT) -I$(HERO_PULP_INC_DIR)

$(PBMK_ROOT)/libpolybench-host.a:
	${HERO_TOOLCHAIN_HOST_TARGET}-gcc -O3 $(PBFLAGS) -fPIC -c $(PBMK_ROOT)/polybench.c -o $(PBMK_ROOT)/polybench.o
	${HERO_TOOLCHAIN_HOST_TARGET}-ar rcs $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/polybench.o

$(PBMK_ROOT)/libpolybench-pulp.a:
	riscv32-hero-unknown-elf-gcc -O3 $(PBFLAGS) $(PBFLAGS_PULP) -fPIC -DPULP -c $(PBMK_ROOT)/polybench.c -o $(PBMK_ROOT)/polybench.o
	riscv32-hero-unknown-elf-ar rcs $(PBMK_ROOT)/libpolybench-pulp.a $(PBMK_ROOT)/polybench.o

polybench-clean:
	rm -rf $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/libpolybench-pulp.a
	rm -rf $(PBMK_ROOT)/build

polybench: $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/libpolybench-pulp.a
