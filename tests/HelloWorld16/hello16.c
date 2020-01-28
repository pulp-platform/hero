#include <pulp.h>

//#include "parMatrixMul.h"

#define N_ITERS 1

//#define CHECKSUM 

#ifdef CHECKSUM
#define CHKSM 88408
#endif


void hello16(testresult_t *result, void (*start)(), void (*stop)());

testcase_t testcases[] = {
  { .name = "Hello World", .test = hello16 },
  {0, 0}
};

int main() {

   if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);
   
  int nbErrors = run_suite(testcases);

  synch_barrier();

  return nbErrors != 0;
}

void hello16(testresult_t *result, void (*start)(), void (*stop)()) {
  int coreid = get_core_id();
  int numcores = get_core_num();

  start();

  printf("Hello from core %d in cluster 0\n", coreid);

  synch_barrier();
  
  if (coreid == 0){
    printf("End of the cluster workload \n");
  }

  synch_barrier();
  stop();
  

}
