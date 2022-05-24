CC := $(HERO_INSTALL)/bin/clang
OBJDUMP := $(HERO_INSTALL)/bin/llvm-objdump


CFLAGS += -target riscv32-unknown-elf --sysroot=$(HERO_INSTALL)/riscv32-unknown-elf
CFLAGS += -target riscv32-unknown-elf -mcpu=snitch -mcmodel=medany -ffast-math -fno-builtin-printf -fno-common
CFLAGS += -menable-experimental-extensions -ffunction-sections -Wextra -static -mno-relax
CFLAGS += -mllvm -enable-misched=false

LIBPATHS += -L$(SNITCH_SDK)/lib/static/
LDFLAGS  += $(ldflags) -static -lsnRuntime-cluster

LDFLAGS  += -T$(SNITCH_SDK)/lib/common.ld
LDFLAGS  += -nostartfiles -fuse-ld=lld -Wl,--image-base=0x80000000
LDFLAGS  += -static
LDFLAGS  += -Wl,-z,norelro -Wl,--gc-sections -Wl,--no-relax

INCPATHS += -I$(SNITCH_SDK)/include

EXE = $(shell basename `pwd`)
SRC = $(CSRCS)

DEPDIR := .deps
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

all: $(DEPS) $(EXE) $(EXE).S

%.o: %.c $(DEPDIR)/%.d | $(DEPDIR)
	$(CC) $(DEPFLAGS) $(CFLAGS) $(INCPATHS) -c $< -o $@

objs := $(patsubst %.c, %.o, $(SRC))
$(EXE): $(objs)
	$(CC) $(LIBPATHS) $(CFLAGS) $(LDFLAGS) $(objs) -o $@

$(EXE).S: $(EXE)
	$(OBJDUMP) -d $^ > $@

# Dep management
$(DEPDIR):
	@mkdir -p $@

DEPFILES := $(CSRCS:%.c=$(DEPDIR)/%.d)
$(DEPFILES):

include $(wildcard $(DEPFILES))

# Phony targets
.PHONY: clean deploy
clean:
	-rm -vf $(EXE) *.S *.o
	-rm -rvf $(DEPDIR)

deploy: $(EXE)
	rsync $(EXE) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/snitch_$(EXE)