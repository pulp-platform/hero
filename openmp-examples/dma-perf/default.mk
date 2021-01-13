ifndef PULP_SDK_HOME
$(error PULP_SDK_HOME is not set)
endif

ifndef_any_of = $(filter undefined,$(foreach v,$(1),$(origin $(v))))

############## Name of output executable file
ifndef EXE
EXE=$(shell basename $(PWD))
endif

EXT_DEF=
############## Default compiler and possible option sets
CC      = $(CROSS_COMPILE)gcc
LD      = $(CROSS_COMPILE)ld
AS      = $(CROSS_COMPILE)gcc
OBJCOPY = $(CROSS_COMPILE)objcopy
OBJDUMP = $(CROSS_COMPILE)objdump
OPT     =-v -O3 -g3 -fopenmp
#
############## Includes
INCDIR        += -I. -I../common -I${HERO_SDK_DIR}/libhero-target/inc
COMMON_CFLAGS += ${INCDIR}
CFLAGS        += $(OPT) -Wall $(COMMON_CFLAGS) ${EXT_DEF}
ASFLAGS       += $(OPT) $(COMMON_CFLAGS)
LDFLAGS       += -L${HERO_SDK_DIR}/libhero-target/lib -lhero-target

############################ OBJECTS ###################################
COBJS  = $(CSRCS:.c=.o)
ASOBJS = $(ASSRCS:.S=.o)
OBJS = $(COBJS) $(ASOBJS)

all: $(EXE)

$(EXE): $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LDFLAGS) -o $@

.PHONY: clean prepare run
clean::
	rm -rf *.o *~ $(EXE) $(OBJS) offload.bin offload.so

init-target-host:
ifndef HERO_TARGET_HOST
$(error HERO_TARGET_HOST is not set)
endif
	ssh -t $(HERO_TARGET_HOST) 'rmmod -f pulp'
	ssh -t $(HERO_TARGET_HOST) 'insmod $(HERO_TARGET_PATH_DRIVER)/pulp.ko'

prepare:: $(EXE)
ifndef HERO_TARGET_HOST
$(error HERO_TARGET_HOST is not set)
endif
	ssh $(HERO_TARGET_HOST) "mkdir -p $(HERO_TARGET_PATH_APPS)"
	scp $(EXE) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/.

run:: prepare $(EXE)
ifeq ($(call ifndef_any_of,HERO_TARGET_HOST HERO_TARGET_PATH_APPS HERO_TARGET_PATH_LIB),)
	ssh -t $(HERO_TARGET_HOST) 'export LD_LIBRARY_PATH='"'$(HERO_TARGET_PATH_LIB)'"'; cd ${HERO_TARGET_PATH_APPS}; ./$(EXE) $(RUN_ARGS)'
else
$(error HERO_TARGET_HOST and/or HERO_TARGET_PATH_APPS is not set)
endif
