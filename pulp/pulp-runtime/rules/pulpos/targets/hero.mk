PULP_LDFLAGS      +=
PULP_CFLAGS       +=  -D__riscv__
PULP_ARCH_CFLAGS ?=  -march=rv32imacxhua20
PULP_ARCH_LDFLAGS ?=  -march=rv32imacxhua20
PULP_ARCH_OBJDFLAGS ?= -Mmarch=rv32imacxhua20
PULP_CFLAGS    += -fdata-sections -ffunction-sections -include chips/hero/config.h -I$(PULPRT_HOME)/include/chips/hero -DARCHI_NO_FC=1 -DARCHI_CL_BOOT=1
PULP_OMP_CFLAGS    += -fopenmp -mnativeomp
PULP_LDFLAGS += -nostartfiles -nostdlib -Wl,--gc-sections -L$(PULPRT_HOME)/kernel -Tchips/hero/link.ld -lgcc

PULP_CC = riscv32-unknown-elf-gcc
PULP_AR ?= riscv32-unknown-elf-ar
PULP_LD ?= riscv32-unknown-elf-gcc
PULP_OBJDUMP ?= riscv32-unknown-elf-objdump

fc/archi=riscv
pe/archi=riscv
pulp_chip=hero
pulp_chip_family=hero
cluster/version=5
fc_itc/version=1
udma/cpi/version=1
udma/i2c/version=2
soc/fll/version=1
udma/i2s/version=2
udma/uart/version=1
event_unit/version=3
perf_counters=True
fll/version=0
padframe/version=1
udma/spim/version=3
gpio/version=3
udma/archi=3
udma/version=3
soc_eu/version=2

# FLL
# PULP_SRCS     += kernel/fll-v$(fll/version).c
# PULP_SRCS     += kernel/freq-domains.c
PULP_SRCS     += kernel/chips/hero/soc.c


include $(PULPRT_HOME)/rules/pulpos/configs/default.mk
include $(PULPRT_HOME)/rules/pulpos/default_rules.mk

# include $(PULPRT_HOME)/rules/pulpos/default_run_target.mk
# customized run target for hero

# TODO: fix this hack
SLM_CONV=~andkurt/bin/slm_conv-0.3

ifeq '$(platform)' 'gvsoc'
run:
	pulp-run --platform=$(platform) --config=$(PULPRUN_TARGET) --dir=$(TARGET_BUILD_DIR) --binary=$(TARGETS) $(runner_args) prepare run
endif

ifeq '$(platform)' 'rtl'

$(TARGET_BUILD_DIR)/modelsim.ini:
	ln -s $(VSIM_PATH)/modelsim.ini $@

$(TARGET_BUILD_DIR)/run_pulp_runtime.tcl:
	ln -s $(VSIM_PATH)/run_pulp_runtime.tcl $@

$(TARGET_BUILD_DIR)/run_common_pre.tcl:
	ln -s $(VSIM_PATH)/run_common_pre.tcl $@

$(TARGET_BUILD_DIR)/run_common_post.tcl:
	ln -s $(VSIM_PATH)/run_common_post.tcl $@

$(TARGET_BUILD_DIR)/compile.tcl:
	ln -s $(VSIM_PATH)/compile.tcl $@

$(TARGET_BUILD_DIR)/start_sim_pulp_runtime.sh:
	ln -s $(VSIM_PATH)/start_sim_pulp_runtime.sh $@

$(TARGET_BUILD_DIR)/sim_common_post.sh:
	ln -s $(VSIM_PATH)/sim_common_post.sh $@

$(TARGET_BUILD_DIR)/compile.sh:
	ln -s $(VSIM_PATH)/compile.sh $@

$(TARGET_BUILD_DIR)/work:
	ln -s $(VSIM_PATH)/work $@

$(TARGET_BUILD_DIR)/pulp_tb.wave.do:
	ln -s $(VSIM_PATH)/../test/pulp_tb.wave.do $@


run: $(TARGETS) $(TARGET_BUILD_DIR)/modelsim.ini $(TARGET_BUILD_DIR)/run_pulp_runtime.tcl \
	$(TARGET_BUILD_DIR)/compile.tcl  $(TARGET_BUILD_DIR)/start_sim_pulp_runtime.sh \
	$(TARGET_BUILD_DIR)/sim_common_post.sh $(TARGET_BUILD_DIR)/run_common_pre.tcl \
	$(TARGET_BUILD_DIR)/run_common_post.tcl \
	$(TARGET_BUILD_DIR)/compile.sh $(TARGET_BUILD_DIR)/pulp_tb.wave.do \
	$(TARGET_BUILD_DIR)/work
# Create L1 SLM
	$(PULP_OBJDUMP) -s --start-address=0x10000000 --stop-address=0x1bffffff $(TARGET_BUILD_DIR)/test/test | rg '^ ' | cut -c 2-45 \
	    | perl -p -e 's/^1b/10/' \
	    | sort \
	    > $(TARGET_BUILD_DIR)/main_l1.slm
	    $(HERO_INSTALL)/bin/one_word_per_line.py $(TARGET_BUILD_DIR)/main_l1.slm

# Create L2 SLM
	$(PULP_OBJDUMP) -s --start-address=0x1c000000 --stop-address=0x1cffffff $(TARGET_BUILD_DIR)/test/test | rg '^ ' | cut -c 2-45 \
	    | sort \
	    > $(TARGET_BUILD_DIR)/main_l2.slm
	    $(HERO_INSTALL)/bin/one_word_per_line.py $(TARGET_BUILD_DIR)/main_l2.slm

# Split SLM per bank
	$(SLM_CONV) --swap-endianness -f "$(TARGET_BUILD_DIR)/main_l1.slm" \
	    -w 32 -P 16 -S 1 -n 2048 -s 0x10000000 -F "$(TARGET_BUILD_DIR)/l1_%01S_%01P.slm"
	$(SLM_CONV) --swap-endianness -f "$(TARGET_BUILD_DIR)/main_l2.slm" \
	    -w 32 -P  4 -S 4 -n 2048 -s 0x1c000000 -F "$(TARGET_BUILD_DIR)/l2_%01S_%01P.slm"

ifdef gui
	export VSIM_FLAGS=+slm_path=.; \
	cd $(TARGET_BUILD_DIR) && ./start_sim_pulp_runtime.sh
else
	export VSIM_FLAGS=+slm_path=.; \
	unset DISPLAY; \
	cd $(TARGET_BUILD_DIR) && ./start_sim_pulp_runtime.sh
endif

endif

# TODO (?)
# ifeq '$(platform)' 'fpga'
# run:
# 	$(PULPRT_HOME)/bin/elf_run_genesys2.sh $(TARGETS)
# endif
