ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

############################ OpenMP Sources ############################
CSRCS = $(wildcard *.c)

# These are PULP-only tests.
only = pulp

-include $(ROOT)/../common/default.mk
