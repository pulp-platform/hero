// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

extern int printf(const char *format, ...);

#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

char buffer[1024 * 1024];

void sweep(int stride)
{
  long instret_start, cycle_start;
  int max_j = 4 * 1024;
  int working_set = max_j * stride;

  for(int i = 0; i < 10; i++)
  {
    if(i == 1)
    {
      instret_start = read_csr(instret);
      cycle_start = read_csr(cycle);
    }

    for(int j = 0; j < max_j; j += 4)
    {
      buffer[(j + 0) * stride] = 0;
      buffer[(j + 1) * stride] = 0;
      buffer[(j + 2) * stride] = 0;
      buffer[(j + 3) * stride] = 0;
    }
  }

  long instrets = read_csr(instret) - instret_start;
  long cycles = read_csr(cycle) - cycle_start;

  printf("working_set = %2dKB, %ld instructions, %ld cycles, CPI = %f\n", 
         working_set / 1024, instrets, cycles, (float) cycles / instrets);
}

int main()
{
  sweep(0);
  sweep(1);
  sweep(2);
  sweep(4);
  sweep(8);
  sweep(16);

  return 0;
}
