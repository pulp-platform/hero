MAKEFLAGS=--warn-undefined-variables

NAME=uart

CC=$(CROSS_COMPILE)gcc
AR=$(CROSS_COMPILE)ar
OB=$(CROSS_COMPILE)objdump

FLAGS=-Wall -O2 ${CFLAGS} -DPLATFORM=${PLATFORM} -I$(HERO_LIBPULP_DIR)/inc -I$(HERO_PULP_INC_DIR)

.PHONY: all build clean deploy dis

all: deploy

$(NAME): $(NAME).c
	$(CC) $(FLAGS) $< -o $@

build: $(NAME)

deploy: build
	scp $(NAME) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/

dis: build
	$(OB) -dS $(NAME).o > $(NAME).disasm

clean:
	-rm -f $(NAME)
