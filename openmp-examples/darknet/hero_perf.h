#ifndef __HERO_PERF_H__
#define __HERO_PERF_H__

#pragma omp declare target
typedef enum {
  CYCLES,         // clock cycles
  CYCLES_ACTIVE,  // active clock cycles (i.e., core not sleeping)
  INSTRS,         // instructions executed
  STALLS_LOAD,    // data load hazards (cycles or events? to be clarified)
} hero_perf_cnt_t;
void hero_perf_enable(hero_perf_cnt_t cnt);
uint32_t hero_perf_get(hero_perf_cnt_t cnt);
void hero_perf_reset(hero_perf_cnt_t cnt);
void hero_perf_reset_all();
#pragma omp end declare target

#endif
