MAKEFLAGS=--warn-undefined-variables

NAME=standalone

CC=$(CROSS_COMPILE)gcc
AR=$(CROSS_COMPILE)ar
OB=$(CROSS_COMPILE)objdump

FLAGS=-Wall -O2 -DPLATFORM=${PLATFORM} ${CFLAGS}

.PHONY: all build clean deploy dis

all: deploy

$(NAME): $(NAME).c $(HERO_LIBPULP_DIR)/lib/libpulp.a
	$(CC) $(FLAGS) $< -static -I$(HERO_LIBPULP_DIR)/inc -L$(HERO_LIBPULP_DIR)/lib \
							  -I$(HERO_PULP_INC_DIR) \
							  -lpulp -lm -o $@

$(HERO_LIBPULP_DIR)/lib/libpulp.a:
	make -C $(HERO_LIBPULP_DIR) lib/libpulp.a

build: $(NAME)

deploy: build
	scp $(NAME) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/

dis: build
	$(OB) -dS $(NAME).o > $(NAME).disasm

clean:
	-rm -f $(NAME)
