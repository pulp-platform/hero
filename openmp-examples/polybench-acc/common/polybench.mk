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

PBFLAGS = -DPOLYBENCH_USE_SCALAR_LB -DPOLYBENCH_TIME -DNUM_TEAMS=1 -DNUM_THREADS=$(threads) -DPOLYBENCH_HERO_MEM_LEVEL=$(mem)

ifneq ($(dma),n)
	PBFLAGS += -DPOLYBENCH_DMA
endif
ifeq ($(dma),device)
	PBFLAGS += -DDMALIB_DEVICE_AS
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
LDFLAGS_COMMON += -ldmatransfer

DEPS += polybench

PBFLAGS_PULP = -DPOLYBENCH_NO_FLUSH_CACHE -DPOLYBENCH_CYCLE_ACCURATE_TIMER
CFLAGS_DMATRANSFER = -I$(PBMK_ROOT) -I$(HERO_PULP_INC_DIR)

$(PBMK_ROOT)/libdmatransfer.a:
	${HERO_TOOLCHAIN_HOST_TARGET}-gcc -O3 $(CFLAGS_DMATRANSFER) $(PBFLAGS) -fPIC -c $(PBMK_ROOT)/dma-lib/dmatransfer-host.c -o $(PBMK_ROOT)/dmatransfer.o
	${HERO_TOOLCHAIN_HOST_TARGET}-ar rcs $(PBMK_ROOT)/libdmatransfer.a $(PBMK_ROOT)/dmatransfer.o

libdmatransfer-pulp:
	cd $(PBMK_ROOT) && $(MAKE) -f $(PBMK_ROOT)/dmatransfer-pulp.mk install

$(PBMK_ROOT)/libpolybench-host.a:
	${HERO_TOOLCHAIN_HOST_TARGET}-gcc -O3 $(PBFLAGS) -fPIC -c $(PBMK_ROOT)/polybench.c -o $(PBMK_ROOT)/polybench.o
	${HERO_TOOLCHAIN_HOST_TARGET}-ar rcs $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/polybench.o

$(PBMK_ROOT)/libpolybench-pulp.a:
	riscv32-hero-unknown-elf-gcc -O3 $(PBFLAGS) $(PBFLAGS_PULP) -fPIC -DPULP -c $(PBMK_ROOT)/polybench.c -o $(PBMK_ROOT)/polybench.o
	riscv32-hero-unknown-elf-ar rcs $(PBMK_ROOT)/libpolybench-pulp.a $(PBMK_ROOT)/polybench.o

polybench-clean:
	rm -rf $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/libpolybench-pulp.a
	rm -rf $(PBMK_ROOT)/libdmatransfer.a
	rm -rf $(PBMK_ROOT)/build

dma-lib: $(PBMK_ROOT)/libdmatransfer.a libdmatransfer-pulp

polybench: dma-lib $(PBMK_ROOT)/libpolybench-host.a $(PBMK_ROOT)/libpolybench-pulp.a
