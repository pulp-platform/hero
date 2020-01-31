#include <pulp.h>

#include "parMatrixMul.h"

#define N_ITERS 1

#define CHECKSUM

#ifdef CHECKSUM
#define CHKSM 88408
#endif

__attribute__ ((section(".heapsram"))) int A[SIZE][SIZE];
__attribute__ ((section(".heapsram"))) int B[SIZE][SIZE];
__attribute__ ((section(".heapsram"))) int C[SIZE][SIZE];


void initialize_mat();

void initialize_mat() {
  int i,j;

  for (i=0;i<SIZE;i++) {
    for (j=0;j<SIZE;j++) {
      A[i][j] = A_init[i][j];
      B[i][j] = B_init[i][j];
    }
  }

}

void matrix_multiplication(testresult_t *result, void (*start)(), void (*stop)());

testcase_t testcases[] = {
  { .name = "Matrix Multiplication", .test = matrix_multiplication },
  {0, 0}
};

int main() {

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);

  int nbErrors = run_suite(testcases);

  synch_barrier();

  return nbErrors != 0;
}

void matrix_multiplication(testresult_t *result, void (*start)(), void (*stop)()) {
  int coreid = rt_core_id();
  int numcores = get_core_num();
  int *CHKSUM_RESULT;
  short int i, iter, j, k;
  int lb, ub, chunk;

  if (coreid == 0){
    printf("Start ParMatrixMul\n",0,0,0,0);
    // initialize matrix A and B
    initialize_mat();
  }
  //number of rows each core has to multiply
  chunk = SIZE / numcores;
  //lower bound
  lb = coreid * chunk;
  //upper bound
  ub = lb + chunk;

  synch_barrier();

  /********************* Benchmark Execution *********************/
  if (coreid<numcores) {
    start();

    for (iter = 0; iter < N_ITERS; iter++) {
      for (i = lb; i < ub; i++) {
        for (k = 0; k < SIZE; k++) {
          C[i][k] = 0;
          for (j = 0; j < SIZE; j++)
            C[i][k] += A[i][j] * B[j][k];
        }
      }
    }
  }
  synch_barrier();
  stop();

  /********************* Benchmark Execution *********************/

#ifdef CHECKSUM
  if(coreid == 0) {

    int chk = 0;
    for (k = 0; k < SIZE; k++)
      for (j = 0; j < SIZE; j++)
        chk += C[k][j];

    check_uint32(result, "Checksum failed", CHKSM, chk);
  }
#endif
}
