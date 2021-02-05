/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Authors:
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 */

/* Copyright (C) 2005-2014 Free Software Foundation, Inc.
 *
 * This file is part of the GNU OpenMP Library (libgomp).
 *
 * Libgomp is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 *
 * Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * Under Section 7 of GPL version 3, you are granted additional
 * permissions described in the GCC Runtime Library Exception, version
 * 3.1, as published by the Free Software Foundation.
 *
 * You should have received a copy of the GNU General Public License and
 * a copy of the GCC Runtime Library Exception along with this program;
 * see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#ifndef __OFFLOAD_MANAGER_H__
#define __OFFLOAD_MANAGER_H__

#include "hal/mailbox/mailbox_v0.h"

extern void** offload_func_table;
extern uint32_t nb_offload_funcs;
extern void** offload_var_table;
extern uint32_t nb_offload_vars;
extern void *__OFFLOAD_TARGET_TABLE__[];

#define DEBUG_LEVEL_OFFLOAD_MANAGER 0

static inline void
gomp_init_offload_manager()
{
    if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0)
        printf("Starting offload manager.\n");

    uint32_t i;

    offload_func_table = ((void **) __OFFLOAD_TARGET_TABLE__)[0];
    nb_offload_funcs   = ((uint32_t)((void **) __OFFLOAD_TARGET_TABLE__)[1]
                        - (uint32_t)((void **) __OFFLOAD_TARGET_TABLE__)[0]) / 0x4U;
    offload_var_table  = ((void **) __OFFLOAD_TARGET_TABLE__)[2];
    nb_offload_vars    = ((uint32_t)((void **) __OFFLOAD_TARGET_TABLE__)[3]
                        - (uint32_t)((void **) __OFFLOAD_TARGET_TABLE__)[2]) / 0x4U;

    mailbox_write(TO_RUNTIME | 2);
    mailbox_write(nb_offload_funcs);
    mailbox_write(nb_offload_vars);

    if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0) {
        printf("nb_offload_funcs = %d\n", (int)nb_offload_funcs);
        printf("nb_offload_vars  = %d\n", (int)nb_offload_vars);
    }

    if (nb_offload_funcs) {
        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0) {
            printf("offload_func_table @ 0x%x\n", (unsigned int)offload_func_table);
            for (i = 0; i < nb_offload_funcs; i++)
                printf("Function %d @ 0x%x\n", (int)i, (unsigned int)offload_func_table[i]);
        }

        mailbox_write(TO_RUNTIME | nb_offload_funcs);
        for(i = 0; i < nb_offload_funcs; i++)
            mailbox_write((uint32_t) offload_func_table[i]);
    }

    if (nb_offload_vars) {
        if (DEBUG_LEVEL_OFFLOAD_MANAGER > 0) {
            printf("(offload_var_table = 0x%x {", (unsigned int)offload_var_table);
            for (i = 0; i < nb_offload_vars; i++) {
                printf ("Variable %d @ 0x%x ... 0x%x\n", (int)i,
                    (unsigned int)offload_var_table[2*i],
                    (unsigned int)offload_var_table[2*i] + (unsigned int)offload_var_table[2*i+1]);
            }
        }

        mailbox_write(TO_RUNTIME | 2*nb_offload_vars);
        for(i = 0; i < nb_offload_vars; i++) {
            mailbox_write((uint32_t) offload_var_table[2*i]);
            mailbox_write((uint32_t) offload_var_table[2*i+1]);
        }
    }

    return;
}

int gomp_offload_manager ( void );
void target_register_lib (const void *);

#endif
