/*
 * HERO HelloWorld Example Application
 *
 * Copyright 2018 ETH Zurich, University of Bologna
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
#include <hero-target.h> // HERODEV_MEMCPY
#include <omp.h>

#ifndef __HERO_DEV
#include <stdint.h>
#include <stdio.h> // printf()
#define snrt_printf(...)
#endif

#ifdef __HERO_DEV
#include <printf.h>
#include <snrt.h>
#endif

int main(int argc, char *argv[]) {

  printf("cva6 main()\n");

#pragma omp target device(HERODEV_MEMCPY)
  {
    #pragma omp parallel
    snrt_printf("Hello World, I am thread %d of %d\n",
      omp_get_thread_num(), omp_get_num_threads());
  }

  return 0;
}
