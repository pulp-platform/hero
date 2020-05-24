ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS = linked-list.c

prepare::
ifndef HERO_TARGET_HOST
$(error HERO_TARGET_HOST is not set)
endif
	scp *.txt $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/.

-include $(ROOT)/../common/default.mk
