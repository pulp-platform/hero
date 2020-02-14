#include "random_helper.h"

//#define VERBOSE 1

uint8_t heap_l2_1024B[1024] = {
  REPEATINC(1024, UINT8_NUMBER)
  };

__attribute__ ((section(".heapsram")))  uint8_t tcdm_2048B[2048] = {
  REPEATINC(2048, UINT8_ZERO)
  };


uint32_t g_lfsr = 0x356167;

void check_random(testresult_t *result, void (*start)(), void (*stop)());

testcase_t testcases[] = {
  { .name = "test1",       .test = check_random   },
  {0, 0}
};


int main()
{
  run_suite(testcases);

  return 0;
}

void check_random(testresult_t *result, void (*start)(), void (*stop)()) {
  unsigned int i;
  for(i = 0; i < 100; i++) {
#ifdef VERBOSE
    printf("Starting random test %d\n", i);
#endif
    dma_random(result, heap_l2_1024B, 1024, tcdm_2048B, 2048, exp_uint8_number);
  }

  // dma_l2_to_tcdm(result, heap_l2_1024B, 706, 1024, tcdm_2048B, 1377, 2048, 318, exp_uint8_number);
}
