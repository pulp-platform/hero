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

CFLAGS		:= -Wall -O2 -fPIC -DPLATFORM=$(PLATFORM) $(CFLAGS)
CFLAGS_SO   := $(CFLAGS) -shared
CC          := $(CROSS_COMPILE)gcc
AR          := $(CROSS_COMPILE)ar
OBJCDUMP    := $(CROSS_COMPILE)objdump

SRCS   := vendor/shmall/llist.c vendor/shmall/heap.c src/pulp.c
OBJS   := $(SRCS:%.c=%.o)
LIBDIR := lib
SO     := $(LIBDIR)/libpulp.so
A      := $(LIBDIR)/libpulp.a

COMPILE.c = $(CC) $(DEPFLAGS) $(CFLAGS) -c

vendor/shmall/%.o : vendor/shmall/%.c $(DEPDIR)/vendor/shmall/%.d | $(DEPDIR)/vendor/shmall
	$(COMPILE.c) -Ivendor/shmall/include -Iinc -o $@ $<

%.o : %.c
src/%.o : src/%.c $(DEPDIR)/src/%.d | $(DEPDIR)
	$(COMPILE.c) -Iinc -I$(HERO_PULP_INC_DIR) -o $@ $<

$(SO): $(OBJS) | $(LIBDIR)
	$(CC) $(CFLAGS_SO) -o $@ $^

$(A): $(OBJS) | $(LIBDIR)
	$(AR) rvs -o $@ $^

$(LIBDIR): ; @mkdir -p $@

$(DEPDIR): ; @mkdir -p $@
$(DEPDIR)/src: ; @mkdir -p $@
$(DEPDIR)/vendor/shmall: ; @mkdir -p $@

DEPFILES := $(SRCS:%.c=$(DEPDIR)/%.d)
$(DEPFILES):

include $(wildcard $(DEPFILES))

.PHONY: all build clean deploy

all: build deploy

build: $(SO) $(A)

clean:
	-rm -rf $(DEPDIR)
	-rm -rf $(LIBDIR)
	-rm -f $(OBJS)

deploy:
	scp $(LIBDIR)/* $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_LIB)
