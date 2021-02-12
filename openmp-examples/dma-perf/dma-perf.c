/*
 * HERO DMA Performance Benchmark
 *
 * Copyright 2020 ETH Zurich, University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <hero-target.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint16_t lfsr3(uint16_t prev) {
  prev ^= prev >> 7;
  prev ^= prev << 9;
  prev ^= prev >> 13;
  return prev;
}

unsigned benchmark_l3(const unsigned buf_size_kib) {
  const unsigned buf_size_bytes = buf_size_kib * 1024;

  // Allocate source and destination buffers on heap of Host.
  uint8_t* const src_buf = (uint8_t*)malloc(buf_size_bytes);
  uint8_t* const dst_buf = (uint8_t*)malloc(buf_size_bytes);
  if (src_buf == NULL || dst_buf == NULL) {
    printf("Error: malloc() on host failed!\n");
    exit(-1);
  }

  // Initialize source buffer with pseudo-random data.
  const uint16_t lfsr_init = 0xB1AAu;
  uint16_t lfsr = lfsr_init;
  for (unsigned i = 0; i < buf_size_bytes / 2; i++) {
    ((uint16_t*)src_buf)[i] = lfsr;
    lfsr = lfsr3(lfsr);
  }

  unsigned cyc_31, cyc_13;
  // clang-format off
  #pragma omp target device(BIGPULP_MEMCPY) \
      map(to: buf_size_bytes, src_buf[0:buf_size_bytes]) \
      map(from: cyc_13, cyc_31, dst_buf[0:buf_size_bytes])
  // clang-format on
  {
    __device uint32_t* const buf_l1 = (__device uint32_t*)hero_l1malloc(buf_size_bytes);
    if (buf_l1 == NULL) {
      printf("ERROR: hero_l1malloc() failed\n");
      abort();
    }

    // L1 to L3 (RAM) with DMA
    cyc_31 = hero_get_clk_counter();
    hero_memcpy_host2dev(buf_l1, (__host void*)src_buf, buf_size_bytes);
    cyc_31 = hero_get_clk_counter() - cyc_31;

    // L3 (RAM) to L1 with DMA
    cyc_13 = hero_get_clk_counter();
    hero_memcpy_dev2host((__host void*)dst_buf, buf_l1, buf_size_bytes);
    cyc_13 = hero_get_clk_counter() - cyc_13;

    hero_l1free(buf_l1);
  }

  // Free source buffer.  We do not use it to compare with the destination buffer because they could
  // be both corrupted in the same way.
  free(src_buf);

  // Compare destination buffer to pseudo-random values.
  unsigned mismatches = 0;
  lfsr = lfsr_init;
  for (unsigned i = 0; i < buf_size_bytes / 2; i++) {
    if (((uint16_t*)dst_buf)[i] != lfsr) {
      mismatches++;
      printf("[%04d] 0x%04x != 0x%04x\n", i, ((uint16_t*)dst_buf)[i], lfsr);
    }
    lfsr = lfsr3(lfsr);
  }

  // Free destination buffer.
  free(dst_buf);

  // Print result.
  printf("For transfer size %d KiB:\n", buf_size_kib);
  if (mismatches == 0) {
    const double perf_31 = ((double)buf_size_bytes) / cyc_31;
    const double perf_13 = ((double)buf_size_bytes) / cyc_13;
    printf("L3 -> L1 DMA: %.3f bytes/cycle\n", perf_31);
    printf("L1 -> L3 DMA: %.3f bytes/cycle\n", perf_13);
  } else {
    printf("%d mismatches!\n", mismatches);
  }

  return mismatches;
}

int main(int argc, char* argv[]) {
  // Test a couple different buffer sizes up to the maximum the L1 heap can allocate.
  unsigned mismatches = 0;
  unsigned buf_size_kib[] = {1, 2, 4, 8, 16, 32, 64, 96, 110};
  for (unsigned i = 0; i < sizeof(buf_size_kib) / sizeof(unsigned); i++) {
    mismatches += benchmark_l3(buf_size_kib[i]);
  }

  return mismatches != 0;
}
