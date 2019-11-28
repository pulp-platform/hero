MAKEFLAGS=--warn-undefined-variables

NAME=standalone

CC=$(CROSS_COMPILE)gcc
AR=$(CROSS_COMPILE)ar
OB=$(CROSS_COMPILE)objdump

CFLAGS+=-Wall -O2 -DPLATFORM=${PLATFORM}
ifneq ($(HERO_LIBPULP_DIR),)
    CFLAGS+=-I$(HERO_LIBPULP_DIR)/inc -L$(HERO_LIBPULP_DIR)/lib
endif

.PHONY: all build clean deploy dis

all: deploy

$(NAME): $(NAME).c
	$(CC) $(CFLAGS) $< -static -idirafter $(HERO_PULP_INC_DIR) \
							  -lpulp -lm -o $@

build: $(NAME)

deploy: build
	scp $(NAME) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/

dis: build
	$(OB) -dS $(NAME).o > $(NAME).disasm

clean:
	-rm -f $(NAME)
