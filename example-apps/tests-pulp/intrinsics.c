#include <stdlib.h>

#include "omp.h"
#include "test.h"

// FIXME: copied from pulp.h which cannot yet be included directly
#define ARCHI_CLUSTER_ADDR 0x1B000000
#define ARCHI_DEMUX_PERIPHERALS_OFFSET 0x204000
#define ARCHI_DEMUX_PERIPHERALS_ADDR ( ARCHI_CLUSTER_ADDR + ARCHI_DEMUX_PERIPHERALS_OFFSET )
#define ARCHI_EU_DEMUX_OFFSET 0x00000
#define ARCHI_EU_DEMUX_ADDR ( ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_EU_DEMUX_OFFSET )
#define EU_CORE_MASK 0x00
#define EU_CORE_EVENT_WAIT 0x38
#define EU_CORE_BUFFER_CLEAR 0x28
#define EU_SW_EVENTS_DEMUX_OFFSET 0x0100
#define EU_CORE_TRIGG_SW_EVENT 0x00

#if defined(__GNUC__)
  #define __builtin_bitinsert(dst, src, size, off) \
    __builtin_pulp_binsert((dst), ~(((1<<(size))-1)<<(off)), (src), (((1<<(size))-1)<<(off)), (off))
#endif

// test bit extensions
unsigned check_bitext()
{
  unsigned n_errors = 0;
  // Prevent compiler optimization
  volatile unsigned val = 0;
  val = 31;
  n_errors += (__builtin_pulp_fl1(val) != 4);
  val = 32;
  n_errors += (__builtin_pulp_fl1(val) != 5);
  val = 0;
  n_errors += (__builtin_pulp_fl1(val) != 32);
  int bits = 0;
  val = 7;
  bits = __builtin_bitinsert(0, val, 1, 3);
  n_errors += (bits != 8); //01000
  val = 5;
  bits = __builtin_bitinsert(bits, val, 2, 7);
  n_errors += (bits != 136); //0010001000
  return n_errors;
}

// test events
unsigned check_events()
{
  unsigned correct = false;

  int sum = 0;
  volatile int *sum_store = &sum;
  #pragma omp parallel num_threads(2)
  {
    if(omp_get_thread_num() == 0) {
      volatile int *mask_addr = (int*)(ARCHI_EU_DEMUX_ADDR + EU_CORE_MASK);
      int prev_mask = *mask_addr;
      *mask_addr = 1;
      __builtin_pulp_event_unit_read((int*)ARCHI_EU_DEMUX_ADDR, EU_CORE_EVENT_WAIT);
      volatile int *clr_addr = (int*)(ARCHI_EU_DEMUX_ADDR + EU_CORE_BUFFER_CLEAR);
      *clr_addr = 1;
      *mask_addr = prev_mask;
      correct = (*sum_store == 1999000);
    } else {
      bool frst = false;
      for(int i=0; i<2000; ++i) {
        *sum_store += i;
      }
      volatile int *trigg_addr = (int*)(ARCHI_EU_DEMUX_ADDR + EU_SW_EVENTS_DEMUX_OFFSET + EU_CORE_TRIGG_SW_EVENT);
      *trigg_addr = 1;
    }
  }
  // omp_set_num_threads(8);
  return !correct;
}

unsigned test_intrinsics()
{
  unsigned n_errors = 0;
  printf("Checking PULP bit manipulation intrinsics\n");
  n_errors += check_bitext();
  printf("Checking PULP event intrinsics\n");
  n_errors += check_events();

  return n_errors;
}
