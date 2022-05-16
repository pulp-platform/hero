MAKEFLAGS=--warn-undefined-variables

NAME=standalone

CC=$(CROSS_COMPILE)gcc
AR=$(CROSS_COMPILE)ar
OB=$(CROSS_COMPILE)objdump

CFLAGS+=-Wall -O2 -DPLATFORM=${PLATFORM}
ifneq ($(HERO_LIBSNITCH_DIR),)
    CFLAGS+=-I$(HERO_LIBSNITCH_DIR)/inc -L$(HERO_LIBSNITCH_DIR)/lib
endif

.PHONY: all build clean deploy dis

all: deploy

$(NAME): $(NAME).c
	@echo " CC      $@"
	$(CC) $(CFLAGS) $< -static -lsnitch -lm -o $@

build: $(NAME)

deploy: build
	rsync $(NAME) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/

dis: build
	$(OB) -dS $(NAME).o > $(NAME).disasm

clean:
	-rm -f $(NAME)
