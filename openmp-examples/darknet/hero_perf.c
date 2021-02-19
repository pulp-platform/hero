#include "hero_perf.h"

#ifndef __PULP__
#include <stdio.h>
#define not_implemented fprintf(stderr, "Function not implemented!\n");
#else
#define CL_CYCLE_COUNT_BASE 0x1B200400
#endif

void hero_perf_reset_all() {
#if defined __PULP__
  *(volatile uint32_t*)(CL_CYCLE_COUNT_BASE + 0x20) = 1;
  asm volatile("csrw 0x79F, 0" : : : "memory");
#else
  not_implemented
#endif
}

uint32_t hero_perf_get(hero_perf_cnt_t cnt) {
#if defined __PULP__
#define csr_read_val(addr) asm volatile("csrr %0, " #addr : "=r"(val) : : "memory");
  uint32_t val;
  switch (cnt) {
    case CYCLES:
      val = *(volatile uint32_t*)(CL_CYCLE_COUNT_BASE + 0x8);
      break;
    case CYCLES_ACTIVE:
      csr_read_val(0x780);
      break;
    case INSTRS:
      csr_read_val(0x781);
      break;
    case STALLS_LOAD:
      csr_read_val(0x782);
      break;
  }
  return val;
#else
  not_implemented
#endif
}

void hero_perf_enable(hero_perf_cnt_t cnt) {
#if defined __PULP__
  if (cnt == CYCLES) {
    *(volatile uint32_t*)(CL_CYCLE_COUNT_BASE + 0x18) = 1;
  } else {
    const uint32_t mask = 1 << (cnt - 1);
    asm volatile("csrs 0xCC0, %0" : : "r"(mask) : "memory");
  }
#else
  not_implemented
#endif
}
