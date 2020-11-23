# Common configuration for all tests of the HERO build infrastructure in
# default.mk.

# These are PULP-only tests.
only = pulp

# Set flags used by all tests
CFLAGS_PULP += -DNO_MAIN -DNO_DOUBLE -I../include
