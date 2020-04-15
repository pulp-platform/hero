CC := riscv32-hero-unknown-elf-gcc

TARGET_DEV = riscv32-hero-unknown-elf

ARCH_DEV = openmp-$(TARGET_DEV)

DEV_OBJDUMP := $(TARGET_DEV)-objdump

ifeq ($(strip $(opt)),)
  opt = 3
endif

.DEFAULT_GOAL = all
DEFMK_ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Take the config name to link to proper libraries
CURRENT_CONFIG_NAME := $(shell echo $(PULP_CURRENT_CONFIG) | cut -d '@' -f 1)
# CURRENT_CONFIG_NAME := $(echo $(PULP_CURRENT_CONFIG) | cut -d '@' -f 1)

# CFLAGS and LDFLAGS have three components/stages
# 1) without suffix, they apply to heterogeneous compilation;
# 2) with _PULP suffix, they apply only to the PULP part of compilation;
# 3) with _COMMON suffix, they apply to both PULP and host compilation.
CFLAGS_COMMON += $(cflags) -O$(opt)
LDFLAGS_COMMON ?= $(ldflags)

CFLAGS_COMMON += -D__device= -D__PULP__ -fopenmp
CFLAGS_PULP   += $(CFLAGS_COMMON) -march=rv32imacXhua20
LDFLAGS_PULP  += $(LDFLAGS_COMMON)
LDFLAGS_PULP  += $(PULP_SDK_INSTALL)/lib/$(CURRENT_CONFIG_NAME)/rt/crt0.o
LDFLAGS_PULP  += $(PULP_SDK_INSTALL)/hero/$(CURRENT_CONFIG_NAME)/rt_conf.o
LDFLAGS_PULP  += -nostdlib -nostartfiles
LDFLAGS_PULP  += -L$(HERO_INSTALL)/riscv32-unknown-elf/lib
LDFLAGS_PULP  += -L$(HERO_INSTALL)/lib/gcc/riscv32-unknown-elf/7.1.1
LDFLAGS_PULP  += -L$(PULP_SDK_INSTALL)/lib/$(CURRENT_CONFIG_NAME)
LDFLAGS_PULP  += -T$(PULP_SDK_INSTALL)/hero/$(CURRENT_CONFIG_NAME)/config.ld
LDFLAGS_PULP  += -T$(PULP_SDK_INSTALL)/hero/omptarget.ld
# Libraries in correct order
LIBS += -lgomp -lomptarget-pulp -lomp -lrt -lrtio -lrt -lhero-target -lvmm -larchi_host -lrt -larchi_host -lm -lc -lgcc -lc

INCPATHS += -I$(DEFMK_ROOT)
INCPATHS += -I$(DEFMK_ROOT)/gcc
INCPATHS += -I$(DEFMK_ROOT)/../../support/libhero-target/inc

LIBPATHS ?=

BENCHMARK = $(shell basename `pwd`)
EXE = $(BENCHMARK)
SRC = $(CSRCS)

DEPDIR := .deps
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

AS_ANNOTATE_ARGS ?=

.PHONY: all exe clean
.PRECIOUS: %.ll %.o

all : $(DEPS) $(EXE) $(EXE).dis slm

%.o: %.c $(DEPDIR)/%.d | $(DEPDIR)
	$(CC) -c $(DEPFLAGS) $(CFLAGS_PULP) $(INCPATHS) -mnativeomp $<

$(EXE): $(SRC:.c=.o)
	touch libgomp.spec
	$(CC) $(LIBPATHS) $(CFLAGS_PULP) $^ $(LDFLAGS_PULP) $(LIBS) -o $@

slm: $(EXE)_l1.slm $(EXE)_l2.slm

$(EXE)_l2.slm: $(EXE)
	$(DEV_OBJDUMP) -s --start-address=0x1c000000 --stop-address=0x1cffffff $^ | rg '^ ' | cut -c 2-45 \
      | sort \
      > $@
	$(DEFMK_ROOT)/one_word_per_line.py $@

$(EXE)_l1.slm: $(EXE)
	$(DEV_OBJDUMP) -s --start-address=0x10000000 --stop-address=0x1bffffff $^ | rg '^ ' | cut -c 2-45 \
      | perl -p -e 's/^1b/10/' \
      | sort \
      > $@
	$(DEFMK_ROOT)/one_word_per_line.py $@

$(EXE).dis: $(EXE)
	$(DEV_OBJDUMP) -d $^ > $@

$(DEPDIR):
	@mkdir -p $@

DEPFILES := $(CSRCS:%.c=$(DEPDIR)/%.d)
$(DEPFILES):

include $(wildcard $(DEPFILES))

clean::
	-rm -vf __hmpp* $(EXE) *~ *.dis *.ll *.slm *.o *.s
	-rm -rvf $(DEPDIR)
