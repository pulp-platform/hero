/*
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

#ifndef __BENCH_H__
#define __BENCH_H__

#include <hero-target.h>

#include <errno.h>    // error codes
#include <stdarg.h>   // va_list, va_end(), va_start()
#include <stdio.h>    // fclose(), fgets(), fopen(), printf(), vprintf()
#include <stdlib.h>   // stdtoul()
#include <time.h>     // clock_gettime(), timespec
#include <unistd.h>   // access()

static struct timespec bench_ts_start, bench_ts_stop;

/**
 * Start benchmark measurement: print label and capture start time.
 */
static inline void bench_start(const char* const format, ...);

/**
 * Stop benchmark measurement: capture stop time and print results.
 *
 * @return  Time since the last `bench_start`, in miliseconds.
 */
static inline double bench_stop(void);

#ifdef __PULP__

static unsigned last_bench_start_time;

// FIXME: Implement benchmarking properly in standalone
static inline void bench_start(const char* const format, ...) {
  __device const char *format_dev = (__device const char*)format;
  printf("BENCH -- %s!\n", format_dev);
  last_bench_start_time = hero_get_clk_counter();
}

static inline double bench_stop(void) {
  const unsigned stop_time = hero_get_clk_counter();
  const unsigned time = stop_time - last_bench_start_time;
  printf("BENCH cycles %d!\n", time);
  return time;
}

#else

/**
 * Get host clock frequency, in MHz.
 *
 * @return  Positive value (clock frequency of host in MHz) on success; negative value with an errno
 *          on failure.
 */
static int get_host_clk_freq_mhz();

void bench_start(const char* const format, ...)
{
  printf("\n");
  va_list arg_ptr;
  va_start(arg_ptr, format);
  vprintf(format, arg_ptr);
  va_end(arg_ptr);
  printf("\n");
  clock_gettime(CLOCK_MONOTONIC_RAW, &bench_ts_start);
}

static inline unsigned long long __ts_to_nsec(const struct timespec* const ts)
{
  return (unsigned long long)ts->tv_sec * 1000000000 + (unsigned long long)ts->tv_nsec;
}

static inline double bench_stop(void)
{
  clock_gettime(CLOCK_MONOTONIC_RAW, &bench_ts_stop);
  const unsigned long long ns = __ts_to_nsec(&bench_ts_stop) - __ts_to_nsec(&bench_ts_start);
  const double ms = ns / 1e6;
  const unsigned long long host_cycles = (ns / 1000) * get_host_clk_freq_mhz();
  printf("Execution time [host cycles] = %llu (%.3f ms)\n", host_cycles, ms);
  return ms;
}

static int get_host_clk_freq_mhz()
{
  const char sysfs_path[] = "/sys/devices/system/cpu/cpufreq/policy0/cpuinfo_cur_freq";
  int ret = access(sysfs_path, F_OK);
  if (ret != 0) {
    printf("ERROR: Could not access '%s'!\n", sysfs_path);
    return ret;
  }

  FILE* const fp = fopen(sysfs_path, "r");
  if (fp == NULL) {
    printf("ERROR: Could not open '%s'!\n", sysfs_path);
    return -EACCES;
  }

  char host_clk_freq_khz_str[20];
  if (fgets(host_clk_freq_khz_str, 20, fp) == NULL) {
    printf("ERROR: Could not read '%s'!\n", sysfs_path);
    return -EIO;
  }
  const unsigned host_clk_freq_mhz = (strtoul(host_clk_freq_khz_str, NULL, 10) + 1) / 1000;

  fclose(fp);

  return host_clk_freq_mhz;
}

#endif

#endif
