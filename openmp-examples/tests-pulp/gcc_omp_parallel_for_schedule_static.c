#include <stdio.h>
#include <omp.h>
#include <stdlib.h>
int gcc_omp_parallel_for_schedule_static (void)
{
  int buf[64], *p;
  int i;
  int result = 0;
  memset (buf, '\0', sizeof (buf));

// #pragma omp parallel for
//   for (i = 0; i < omp_get_num_threads(); i++){
//     if(omp_get_thread_num()!=i){
//       printf("Error: for loop is not executed in parallel\n");
//       result = 1;
//     }
//   }
//   printf("Parallel for is exceuted correctly\n");
  // printf("Buffer address %8x\n",  (unsigned) buf);
  // #pragma omp parallel for schedule (static, 3)
  // for (i = 10; i < 54; i++)
  //   buf[i] = 5;
  // for (i = 0; i < 64; i++)
  //   printf("Buffer %d: %d\n", i, buf[i]);
  //   if (buf[i] != 5 * (i >= 10 && i < 54)){
  //     printf("error 21 at loop-5\n");
  //     result += 1;
  //   }
  // printf("success 0\n");
  // memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3) private(p)
  // for 
  for (p = &buf[10]; p < &buf[54]; p++)
    // printf("&p = ")
    *p = 5;
  for (i = 0; i < 64; i++)
    printf("Buffer %d: %d\n", i, buf[i]);
    if (buf[i] != 5 * (i >= 10 && i < 54)){
      printf("error 21 at loop-5\n");
      result += 1;
    }
  printf("success 1\n");
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[3]; p <= &buf[63]; p += 2)
    p[-2] = 6;
  for (i = 0; i < 64; i++)
    if (buf[i] != 6 * ((i & 1) && i <= 61)){
      printf("error 22 at loop-5\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[16]; p < &buf[51]; p = 4 + p)
    p[2] = 7;
  for (i = 0; i < 64; i++)
    if (buf[i] != 7 * ((i & 3) == 2 && i >= 18 && i < 53)){
      printf("error 23 at loop-5\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[16]; p <= &buf[40]; p = p + 4ULL)
    p[2] = -7;
  for (i = 0; i < 64; i++)
    if (buf[i] != -7 * ((i & 3) == 2 && i >= 18 && i <= 42)){
      printf("error 24 at loop-5\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[53]; p > &buf[9]; --p)
    *p = 5;
  for (i = 0; i < 64; i++)
    if (buf[i] != 5 * (i >= 10 && i < 54)){
      printf("error 25 at loop-5\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[63]; p >= &buf[3]; p -= 2)
    p[-2] = 6;
  for (i = 0; i < 64; i++)
    if (buf[i] != 6 * ((i & 1) && i <= 61)){
      printf("error 26 at loop-5\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[48]; p > &buf[15]; p = -4 + p)
    p[2] = 7;
  for (i = 0; i < 64; i++)
    if (buf[i] != 7 * ((i & 3) == 2 && i >= 18 && i < 53)){
      printf("error 27 at loop-5\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[40]; p >= &buf[16]; p = p - 4ULL)
    p[2] = -7;
  for (i = 0; i < 64; i++)
    if (buf[i] != -7 * ((i & 3) == 2 && i >= 18 && i <= 42)){
      printf("error 28 at loop-5\n");
      result += 1;
    }
  return (result == 0);
}

// int main()
// {
//   printf("result:%d\n", test_ompgcc_for_schedule_static());
// }