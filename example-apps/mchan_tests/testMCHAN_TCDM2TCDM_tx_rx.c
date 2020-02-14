#include "pulp.h"
#include "mchan_tests.h"
#include "archi/pulp.h"

#define VERBOSE

#define MAX_BUFFER_SIZE 0x2000

L2_DATA static  char ext_src[MAX_BUFFER_SIZE];
L1_DATA static  char loc_src[MAX_BUFFER_SIZE];
L2_DATA static  char ext_dst[MAX_BUFFER_SIZE];
L1_DATA static  char loc_dst[MAX_BUFFER_SIZE];


#define EXT_DATA_SRC_ADDR  ( ext_src)
#define TCDM_DATA_SRC_ADDR ( loc_src)
#define EXT_DATA_DST_ADDR  ( ext_dst)
#define TCDM_DATA_DST_ADDR ( loc_dst)

int testMCHAN(unsigned int len, char incr, char twd, unsigned short int count, unsigned short int stride);

int main()
{
  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);
  
  int   i,error_count = 0;
  
  if (get_core_id() == 0)
  {
    
    for (i=8; i<8192; i=i*2){
      error_count += testMCHAN(i, INC, LIN, 0, 0);
    }  
    
  }
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char incr, char twd, unsigned short int count, unsigned short int stride){
  
  volatile unsigned int i,j,id1,id2;
  volatile int test,read,error=0;
  
  printf ("STARTING TEST FOR %d TX AND RX CONCURRENT OPERATIONS: \n",len);
  
  for (i=0; i<len/4; i++){
    *(int*)(EXT_DATA_SRC_ADDR + 4*i) = 0xFF000000 + i;
  }
  
  for (i=0; i<len/4; i++){
    *(int*)(TCDM_DATA_SRC_ADDR + 4*i) = 0xFF010000 + i;
  }
  
  id1 = mchan_alloc();
  
  mchan_transfer(len, RX, incr, twd, 0, 1, 0, 0, (unsigned int)(EXT_DATA_SRC_ADDR), (unsigned int)(TCDM_DATA_DST_ADDR), 0, 0, 0, 0);
  
  id2 = mchan_alloc();
  
  mchan_transfer(len, TX, incr, twd, 0, 1, 0, 0, (unsigned int)(EXT_DATA_DST_ADDR), (unsigned int)(TCDM_DATA_SRC_ADDR), 0, 0, 0, 0);
  
  mchan_barrier(id1);
  mchan_barrier(id2);
  
  mchan_free(id1);
  mchan_free(id2);
  
  for (i=0; i<len/4; i++){
    
    test = 0xFF000000+i;
    read = *(int*)(TCDM_DATA_DST_ADDR + 4*i);
    
    if ( test != read ){
      printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  for (i=0; i<len/4; i++){
    
    test = 0xFF010000+i;
    read = *(int*)(EXT_DATA_DST_ADDR + 4*i);
    
    if ( test != read ){
      printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  if (error == 0)
    printf ("OOOOOOK!!!!!!\n");
  
  return error;

}
