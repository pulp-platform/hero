# Copyright (C) 2018 ETH Zurich and University of Bologna
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
MAKEFLAGS=--warn-undefined-variables

DEPDIR := .deps
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

CFLAGS		:= -Wall -g -O2 -fPIC -DPLATFORM=$(PLATFORM) $(CFLAGS)
CFLAGS_SO   := $(CFLAGS) -shared
CC          := $(CROSS_COMPILE)gcc
AR          := $(CROSS_COMPILE)ar
OBJCDUMP    := $(CROSS_COMPILE)objdump

SRCS   := src/libsnitch.c src/libsnitch-compat.c src/fesrv.c vendor/o1heap/o1heap/o1heap.c
OBJS   := $(SRCS:%.c=%.o)
LIBDIR := lib
SO     := $(LIBDIR)/libsnitch.so
A      := $(LIBDIR)/libsnitch.a

# include paths
INC_DIRS  := . include ../snitch-driver ../include vendor/o1heap/o1heap $(INC_DIRS)
INC_FLAGS := $(addprefix -I,$(INC_DIRS))

COMPILE.c = $(CC) $(DEPFLAGS) $(CFLAGS) $(INC_FLAGS) -c

vendor/o1heap/o1heap/%.o : vendor/o1heap/o1heap/%.c $(DEPDIR)/vendor/o1heap/o1heap/%.d | $(DEPDIR)/vendor/o1heap/o1heap
	$(COMPILE.c) -Ivendor/o1heap/o1heap -o $@ $<

%.o : %.c
src/%.o : src/%.c $(DEPDIR)/src/%.d | $(DEPDIR)
	$(COMPILE.c) -Iinc -I$(HERO_PULP_INC_DIR) -Ivendor/o1heap/o1heap -o $@ $<

$(SO): $(OBJS) | $(LIBDIR)
	$(CC) $(CFLAGS_SO) -o $@ $^

$(A): $(OBJS) | $(LIBDIR)
	$(AR) rvs -o $@ $^

$(LIBDIR): ; @mkdir -p $@

$(DEPDIR): ; @mkdir -p $@
$(DEPDIR)/src: ; @mkdir -p $@
$(DEPDIR)/vendor/o1heap/o1heap: ; @mkdir -p $@

DEPFILES := $(SRCS:%.c=$(DEPDIR)/%.d)
$(DEPFILES):

include $(wildcard $(DEPFILES))

.PHONY: all build clean deploy

all: build deploy

build: $(SO) $(A)

deploy:
	rsync $(SO) $(HERO_TARGET_HOST):/usr/lib

clean:
	-rm -rf $(DEPDIR)
	-rm -rf $(LIBDIR)
	-rm -f $(OBJS)
