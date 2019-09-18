/*
 * This file is part of the PULP device driver.
 * It is based on arch/arm64/include/asm/assembler.h, arch/arm64/mm/cache.S.
 *
 * Copyright (C) 1996-2000 Russell King
 * Copyright (C) 2001 Deep Blue Solutions Ltd.
 * Copyright (C) 2012 ARM Ltd.
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Custom cache maintenance
 *
 * This is a simplified version of arch/arm64/include/asm/assembler.h and
 * arch/arm64/mm/cache.S based on Linux 4.9 to avoid linker issues due to the
 * alternatives runtime patching framework.
 *
 * This file just contains the macros and assembly sequences absolutely
 * needed by the PULP driver.
 *
 * IMPORTANT: It is assumed that all host cores use the same cache line length
 * and that ARM64_MISMATCHED_CACHE_LINE_SIZE is thus false.
 */

#include <linux/linkage.h>

/***********************************************************************************
 *
 *  █████╗ ███████╗███████╗███████╗███╗   ███╗██████╗ ██╗     ███████╗██████╗    ██╗  ██╗
 * ██╔══██╗██╔════╝██╔════╝██╔════╝████╗ ████║██╔══██╗██║     ██╔════╝██╔══██╗   ██║  ██║
 * ███████║███████╗███████╗█████╗  ██╔████╔██║██████╔╝██║     █████╗  ██████╔╝   ███████║
 * ██╔══██║╚════██║╚════██║██╔══╝  ██║╚██╔╝██║██╔══██╗██║     ██╔══╝  ██╔══██╗   ██╔══██║
 * ██║  ██║███████║███████║███████╗██║ ╚═╝ ██║██████╔╝███████╗███████╗██║  ██║██╗██║  ██║
 * ╚═╝  ╚═╝╚══════╝╚══════╝╚══════╝╚═╝     ╚═╝╚═════╝ ╚══════╝╚══════╝╚═╝  ╚═╝╚═╝╚═╝  ╚═╝
 *
 **********************************************************************************/
/*
 * read_ctr - read CTR_EL0. If the system has mismatched
 * cache line sizes, provide the system wide safe value
 * from arm64_ftr_reg_ctrel0.sys_val
 */
	.macro	read_ctr, reg
	mrs	\reg, ctr_el0			// read CTR
	nop
	.endm

/*
 * dcache_line_size - get the safe D-cache line size across all CPUs
 */
	.macro	dcache_line_size, reg, tmp
	read_ctr	\tmp
	ubfm		\tmp, \tmp, #16, #19	// cache line size encoding
	mov		\reg, #4		// bytes per word
	lsl		\reg, \reg, \tmp	// actual cache line size
	.endm

/* We always call the macro dcache_by_line_op with the civac operation.
 * Thus, we create a new macro.
 */
/*
 * Macro to perform a data cache maintenance for the interval
 * [kaddr, kaddr + size)
 *
 * 	op:		operation passed to dc instruction
 * 	domain:		domain used in dsb instruciton
 * 	kaddr:		starting virtual address of the region
 * 	size:		size of the region
 * 	Corrupts:	kaddr, size, tmp1, tmp2
 */
	.macro dcache_by_line_civac op, domain, kaddr, size, tmp1, tmp2
	dcache_line_size \tmp1, \tmp2
	add	\size, \kaddr, \size
	sub	\tmp2, \tmp1, #1
	bic	\kaddr, \kaddr, \tmp2
9998:
	dc	\op, \kaddr
	add	\kaddr, \kaddr, \tmp1
	cmp	\kaddr, \size
	b.lo	9998b
	dsb	\domain
	.endm

/*
 * Annotate a function as position independent, i.e., safe to be called before
 * the kernel virtual mapping is activated.
 */
#define ENDPIPROC(x)			\
	.globl	__pi_##x;		\
	.type 	__pi_##x, %function;	\
	.set	__pi_##x, x;		\
	.size	__pi_##x, . - x;	\
	ENDPROC(x)

/***********************************************************************************
 *
 *  ██████╗ █████╗  ██████╗██╗  ██╗███████╗   ███████╗
 * ██╔════╝██╔══██╗██╔════╝██║  ██║██╔════╝   ██╔════╝
 * ██║     ███████║██║     ███████║█████╗     ███████╗
 * ██║     ██╔══██║██║     ██╔══██║██╔══╝     ╚════██║
 * ╚██████╗██║  ██║╚██████╗██║  ██║███████╗██╗███████║
 *  ╚═════╝╚═╝  ╚═╝ ╚═════╝╚═╝  ╚═╝╚══════╝╚═╝╚══════╝
 *
 **********************************************************************************/
/*
 *	__flush_dcache_area(kaddr, size)
 *
 *	Ensure that any D-cache lines for the interval [kaddr, kaddr+size)
 *	are cleaned and invalidated to the PoC.
 *
 *	- kaddr   - kernel address
 *	- size    - size in question
 */
ENTRY(__flush_dcache_area)
	dcache_by_line_civac civac, sy, x0, x1, x2, x3
	ret
ENDPIPROC(__flush_dcache_area)
