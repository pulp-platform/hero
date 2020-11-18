/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
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

/*
 * Authors: Germain Haugou, ETH (germain.haugou@iis.ee.ethz.ch)
 */

  .global GOMP_parallel
GOMP_parallel:   
  //c.bnez    a2, GOMP_parallel_notzero
  bnez    a2, GOMP_parallel_notzero
GOMP_parallel_do:   
  lui       t0, 0x204000 >> 12
  sw        a0, 128(t0)
  sw        a1, 128(t0)
  sw        ra, %tiny(parallelTemp0)(x0)
  //c.mv      a2, a0
  //c.mv      a0, a1
  mv      a2, a0
  mv      a0, a1
  jalr      ra, a2
  lw        ra, %tiny(parallelTemp0)(x0)
  p.elw     x0, 0x21c(t0)
  //c.jr      ra
  jr      ra

GOMP_parallel_notzero:
  la        t0, __NB_ACTIVE_PE
  beq       a2, t0, GOMP_parallel_do
  j partialParallelRegion
