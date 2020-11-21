ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

############################ OpenMP Sources ############################
CSRCS = $(wildcard *.c)

# These are PULP-only tests.
only = pulp

CFLAGS_PULP := ${CFLAGS_PULP} -DNO_MAIN -DNO_DOUBLE -I../include

-include $(ROOT)/../../common/default.mk
