PULP_APP = test
PULP_APP_SRCS = $(TEST_SRCS)
PULP_APP_FC_SRCS = $(TEST_FC_SRCS)
ifdef TEST_FC_SRCS
pulpFc=1
endif

space :=
space +=

BUILD_DIR = $(subst $(space),_,$(CURDIR)/build/$(TEST_SRCS))

ifdef VERBOSE
override PULP_CFLAGS += -DVERBOSE
endif

override PULP_CFLAGS += -Os -g 

include $(PULP_SDK_HOME)/install/rules/pulp.mk
