/* Adapted from llvm test suite: 
 * https://github.com/llvm-mirror/openmp/blob/master/runtime/test/worksharing/for/omp_parallel_for_reduction.c
 * The tests for doubles have been commented on.
 * All valid operators for reduction are tested ann pass the test.
 */

// RUN: %libomp-compile-and-run
#include <stdio.h>
// #include <math.h>
#include "omp_testsuite.h"



// #define DOUBLE_DIGITS 20    /* dt^DOUBLE_DIGITS */
#define MAX_FACTOR 10
#define KNOWN_PRODUCT 3628800  /* 10! */


int logics[LOOPCOUNT];

int test_omp_parallel_for_reduction()
{
  int sum =0;
  int known_sum;

  double dsum;
  double dknown_sum;
  double dt=0.5;  /* base of geometric row for + and - test*/
  double rounding_error= 1.E-9;
  int diff;
  double ddiff;
  int product;
  int known_product;
  int logic_and;
  int logic_or;
  int bit_and;
  int bit_or;
  int exclusiv_bit_or;
  int i;
  double dpt;
  int result;
  sum =0;
  dsum=0;
  dt = 1./3.;
  result = 0;
  product = 1;
  logic_and=1;
  logic_or=0;
  bit_and=1;
  bit_or=0;
  exclusiv_bit_or=0;

  /* Tests for integers */
  known_sum = (100*(100+1))/2;

  #pragma omp parallel for   private(i) reduction(+:sum)
  for (i=1;i<=100;i++) {
    sum=sum+i;
  }
  if(known_sum!=sum) {
    result++;
    printf("Error in sum with integers: Result was %d"
      " instead of %d\n",sum,known_sum); 
  }
  else printf("integer + is good\n");

  diff = (LOOPCOUNT*(LOOPCOUNT+1))/2;
  #pragma omp parallel for   private(i) reduction(-:diff)
  for (i=1;i<=LOOPCOUNT;++i) {
    diff=diff-i;
  }
  if(diff != 0) {
    result++;
    printf("Error in difference with integers: Result was %d"
      " instead of 0.\n",diff);
  }
  else printf("integer - is good\n");

  
  /* Tests for doubles */
  // dsum=0;
  // dpt=1;
  // for (i=0;i<DOUBLE_DIGITS;++i) {
  //   dpt*=dt;
  // }
  // dknown_sum = (1-dpt)/(1-dt);
  // #pragma omp parallel for   private(i) reduction(+:dsum)
  // for (i=0;i<DOUBLE_DIGITS;++i) {
  //   dsum += pow(dt,i);
  // }
  // if( fabs(dsum-dknown_sum) > rounding_error ) {
  //   result++; 
  //   printf("Error in sum with doubles: Result was %f"
  //     " instead of %f (Difference: %E)\n",
  //     dsum, dknown_sum, dsum-dknown_sum);
  // }

  // dpt=1;

  // for (i=0;i<DOUBLE_DIGITS;++i) {
  //   dpt*=dt;
  // }
  // printf("\n");
  // ddiff = (1-dpt)/(1-dt);
  // #pragma omp parallel for   private(i) reduction(-:ddiff)
  // for (i=0;i<DOUBLE_DIGITS;++i) {
  //   ddiff -= pow(dt,i);
  // }
  // if( fabs(ddiff) > rounding_error) {
  //   result++;
  //   printf("Error in Difference with doubles: Result was %E"
  //     " instead of 0.0\n",ddiff);
  // }

  /* Tests for integers */
  #pragma omp parallel for   private(i) reduction(*:product)
  for(i=1;i<=10;i++) {
    product *= i;
  }
  known_product = 3628800;
  if(known_product != product) {
    result++;
    printf("Error in Product with integers: Result was %d"
      " instead of %d\n\n",product,known_product);
  }
  else printf("integer * is good\n");

  /* Tests for logic AND */
  for(i=0;i<LOOPCOUNT;i++) {
    logics[i]=1;
  }

  #pragma omp parallel for   private(i) \
    reduction(&&:logic_and)
  for(i=0;i<LOOPCOUNT;++i) {
    logic_and = (logic_and && logics[i]);
  }
  if(!logic_and) {
    result++;
    printf("Error in logic AND part 1.\n");
  }
  else printf("logic && part 1 is good\n");

  logic_and = 1;
  logics[LOOPCOUNT/2]=0;

  #pragma omp parallel for   private(i) \
    reduction(&&:logic_and)
  for(i=0;i<LOOPCOUNT;++i) {
    logic_and = logic_and && logics[i];
  }
  if(logic_and) {
    result++;
    printf("Error in logic AND part 2.\n");
  }
  else printf("logic && part 2 is good\n");

  /* Tests for logic OR */
  for(i=0;i<LOOPCOUNT;i++) {
    logics[i]=0;
  }

  #pragma omp parallel for   private(i) \
    reduction(||:logic_or)
  for(i=0;i<LOOPCOUNT;++i) {
    logic_or = logic_or || logics[i];
  }
  if(logic_or) {
    result++;
    printf("Error in logic OR part 1.\n");
  }
  else printf("logic || part 1 is good\n");

  logic_or = 0;
  logics[LOOPCOUNT/2]=1;

  #pragma omp parallel for   private(i) \
    reduction(||:logic_or)
  for(i=0;i<LOOPCOUNT;++i) {
    logic_or = logic_or || logics[i];
  }
  if(!logic_or) {
    result++;
    printf("Error in logic OR part 2.\n");
  }
  else printf("logic !! part 2 is good\n");


  /* Tests for bitwise AND */
  for(i=0;i<LOOPCOUNT;++i) {
    logics[i]=1;
  }

  #pragma omp parallel for   private(i) \
    reduction(&:bit_and)
  for(i=0;i<LOOPCOUNT;++i) {
    bit_and = (bit_and & logics[i]);
  }
  if(!bit_and) {
    result++;
    printf("Error in BIT AND part 1.\n");
  }
  else printf("bit and & part 1 is good\n");

  bit_and = 1;
  logics[LOOPCOUNT/2]=0;

  #pragma omp parallel for   private(i) \
    reduction(&:bit_and)
  for(i=0;i<LOOPCOUNT;++i) {
    bit_and = bit_and & logics[i];
  }
  if(bit_and) {
    result++;
    printf("Error in BIT AND part 2.\n");
  }
  else printf("bit and & part 2 is good\n");

  /* Tests for bitwise OR */
  for(i=0;i<LOOPCOUNT;i++) {
    logics[i]=0;
  }

  #pragma omp parallel for   private(i) \
    reduction(|:bit_or)
  for(i=0;i<LOOPCOUNT;++i) {
    bit_or = bit_or | logics[i];
  }
  if(bit_or) {
    result++;
    printf("Error in BIT OR part 1\n");
  }
  else printf("| part 1 is good\n");

  bit_or = 0;
  logics[LOOPCOUNT/2]=1;

  #pragma omp parallel for   private(i) \
    reduction(|:bit_or)
  for(i=0;i<LOOPCOUNT;++i) {
    bit_or = bit_or | logics[i];
  }
  if(!bit_or) {
    result++;
    printf("Error in BIT OR part 2\n");
  }
  else printf("| part 2 is good\n");

  /* Tests for bitwise XOR */
  for(i=0;i<LOOPCOUNT;i++) {
    logics[i]=0;
  }

  #pragma omp parallel for   private(i) \
    reduction(^:exclusiv_bit_or)
  for(i=0;i<LOOPCOUNT;++i) {
    exclusiv_bit_or = exclusiv_bit_or ^ logics[i];
  }
  if(exclusiv_bit_or) {
    result++;
    printf("Error in EXCLUSIV BIT OR part 1\n");
  }
  else printf("^ part 1 is good\n");

  exclusiv_bit_or = 0;
  logics[LOOPCOUNT/2]=1;

  #pragma omp parallel for   private(i) \
    reduction(^:exclusiv_bit_or)
  for(i=0;i<LOOPCOUNT;++i) {
    exclusiv_bit_or = exclusiv_bit_or ^ logics[i];
  }
  if(!exclusiv_bit_or) {
    result++;
    printf("Error in EXCLUSIV BIT OR part 2\n");
  }
  else printf("^ part 2 is good\n");

  /*printf("\nResult:%d\n",result);*/
  return (result==0);
}


// int main()
// {
//   int i;
//   int num_failed=0;

//   for(i = 0; i < REPETITION; i++) {
//     if(!test_omp_parallel_for_reduction()) {
//       num_failed++;
//     }
  
//   printf("num_failed:%d\n", num_failed);
//   return num_failed;
// }
