ifeq '$(CONFIG_CRT0)' '1'
PULP_ASM_SRCS += kernel/crt0.S
endif

ifeq '$(CONFIG_LIBC_MINIMAL)' '1'
PULP_SRCS += lib/libc/minimal/io.c lib/libc/minimal/fprintf.c lib/libc/minimal/prf.c lib/libc/minimal/sprintf.c
endif

PULP_SRCS += kernel/init.c kernel/kernel.c kernel/alloc.c kernel/alloc_pool.c kernel/irq.c kernel/soc_event.c kernel/bench.c drivers/uart.c

PULP_ASM_SRCS += kernel/irq_asm.S


ifneq '$(cluster/version)' ''
PULP_SRCS += kernel/cluster.c
endif