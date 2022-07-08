#pragma once

#include <svdpi.h>
#include <vpi_user.h>


#ifdef __cplusplus
extern "C" {
#endif
     extern void write_word_dpi(uint32_t addr, uint32_t data);
     extern void read_word_dpi(uint32_t addr, uint32_t *data);
     extern uint32_t preload_mem_dpi(char *file_name, uint32_t addr);
#ifdef __cplusplus
} // extern "C"
#endif

#define write_word(addr, data)          write_word_dpi(addr, data)
#define read_word(addr, data)           read_word_dpi(addr, data)
#define preload_mem(file_name, data)    preload_mem_dpi(file_name, data)

#define dpi_print1(str)                 vpi_printf(str)
#define dpi_print2(str, arg1)           vpi_printf(str, arg1)
#define dpi_print3(str, arg1, arg2)     vpi_printf(str, arg1, arg2)
