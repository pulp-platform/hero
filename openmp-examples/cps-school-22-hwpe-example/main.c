#include <hero-target.h>
#include <arov-target.h>

#pragma omp declare target
#include "traffic_gen_api.h"

void test()
{
  #pragma omp parallel
  {
    #pragma omp master
    {
      printf("I am the master, and I am going to program the accelerator\n");      
      arov_struct arov;
      int offload_id;
      int cluster_id = 0;
      int acc_id = 0;
      
      __device uint32_t * a_local = (__device uint32_t *)hero_l1malloc(1024*sizeof(uint32_t));

      printf("Initialized the Traffic Gen %d\n", acc_id);
      arov_init(&arov, cluster_id, acc_id);

      printf("Prepare Traffic Gen %d Job descriptor\n", acc_id);
      arov_map_params_traffic_gen(
        &arov, 
        cluster_id, 
        acc_id,
        a_local, /* buffer_l1_base_pointer */
        1024,    /* i/o size in word (I/O) */
        512,     /* input size in word */
        1, 
        1,
        512,     /* total tx generated */
        1,
        1, 
        512,
        1,       /* n_reps */
        16);     /* n_banks touched */

      printf("Program Traffic Gen %d\n", acc_id);
      offload_id = arov_activate(&arov, cluster_id, acc_id);
      arov_program(&arov, cluster_id, acc_id);

      printf("Start Traffic Gen %d\n", acc_id);
      arov_compute(&arov, cluster_id, acc_id);

      printf("Wait for termination Traffic Gen %d\n", acc_id);
      arov_wait(&arov, cluster_id, acc_id);

      arov_free(&arov, cluster_id, acc_id);
      printf("Traffic Gen %d execution is complete!\n", acc_id);
    }

    printf("I am waiting for the termination of all the threads\n");
    #pragma omp barrier
    printf("That s all folks!\n");
  }
}
#pragma omp end declare target


int main(int argc, char *argv[])
{

  #pragma omp target
  test(); 

  return 0;
}