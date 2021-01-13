#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <hero-target.h>

#pragma omp declare target
void mem_copy() {
  printf("Checkpoint 0\n");
  #ifdef __PULP__
  printf("Checkpoint 1\n");
  __prem_dma_memcpy_to_spm_1d(0x10000a60, 0x82000460, 0x4);
  printf("Checkpoint 2\n");
  __prem_dma_memcpy_to_spm_1d(0x10000a64, 0x80000460, 0x3ffc);
  printf("Checkpoint 3\n");
  __prem_dma_memcpy_to_spm_1d(0x10004a60, 0x82000c60, 0x3ffc);
  printf("Checkpoint 4\n");
  __prem_dma_memcpy_to_spm_1d(0x10000a60, 0x82000460, 0x4);
  printf("Checkpoint 5\n");
  __prem_dma_memcpy_from_spm_1d(0x10004a60, 0x82000c60, 0x3ffc);
  printf("Checkpoint 6\n");
  __prem_dma_memcpy_to_spm_1d(0x10000a64, 0x8000445c, 0x3ffc);
  printf("Checkpoint 7\n");
  __prem_dma_memcpy_to_spm_1d(0x10004a60, 0x82004c5c, 0x3ffc);
  printf("Checkpoint 8\n");
  __prem_dma_memcpy_to_spm_1d(0x10000a60, 0x82000460, 0x4);
  printf("Checkpoint 9\n");
  __prem_dma_memcpy_from_spm_1d(0x10004a60, 0x82004c5c, 0x3ffc);
  printf("Checkpoint 10\n");
  #endif
}
#pragma omp end declare target
int main(int argc, char *argv[]) {

  omp_set_default_device(BIGPULP_MEMCPY);
  mem_copy();
  printf("Done!\n");
  return 0;
}
