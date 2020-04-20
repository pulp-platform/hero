/*
 * Copyright 2019 ETH Zurich, University of Bologna
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

#ifndef __TESTS_H__
#define __TESTS_H__

unsigned test_atomic();
unsigned test_dma();
unsigned test_floats();
unsigned test_m_instrs();
unsigned test_memory();
unsigned test_intrinsics();

int test_omp_atomic();
int test_omp_for_schedule_static();
int test_omp_parallel_for_reduction();
int test_omp_barrier();
int test_omp_for_schedule_dynamic();
int test_omp_parallel_for_private();
int test_omp_parallel_for_firstprivate();
int test_omp_parallel_for_lastprivate();
int test_omp_single();
int test_omp_critical();
int test_omp_master_3();
int test_omp_parallel_sections_firstprivate();
int test_omp_parallel_sections_lastprivate();
int test_omp_parallel_sections_private();
int test_omp_parallel_sections_reduction();
int test_omp_section_firstprivate();
int test_omp_section_lastprivate();
int test_omp_section_private();
int test_omp_sections_reduction();

int gcc_omp_parallel_for_schedule_static();
int gcc_omp_parallel_for_schedule_dynamic();
#endif
