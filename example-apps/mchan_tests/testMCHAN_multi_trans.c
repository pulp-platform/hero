//#include "mchan.h"
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE

#define BUFFSIZE_BYTE 0x4000
#define BUFFSIZE (BUFFSIZE_BYTE/4)

L2_DATA static  char ext1[BUFFSIZE_BYTE];
L2_DATA static  char ext2[BUFFSIZE_BYTE];
L1_DATA static  char loc1[BUFFSIZE_BYTE];
L1_DATA static  char loc2[BUFFSIZE_BYTE];

#define EXT_DATA_ADDR_1  ( ext1)
#define EXT_DATA_ADDR_2  ( ext2)
#define TCDM_DATA_ADDR_1 ( loc1)
#define TCDM_DATA_ADDR_2 ( loc2)

int testMCHAN_LDST16384_256();
int testMCHAN_LDST16384_512();
int testMCHAN_LDST16384_1024();
int testMCHAN_LDST16384_2048();

int main()
{

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);
  
  
  int   error_count = 0;
  
  if (rt_core_id() == 0)
  {
        
    error_count += testMCHAN_LDST16384_2048();
    
    error_count += testMCHAN_LDST16384_1024();
    
    error_count += testMCHAN_LDST16384_512();
    
    error_count += testMCHAN_LDST16384_256();
    
#if defined(PMU_VERSION)
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 10000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 80000000);
    
    error_count += testMCHAN_LDST16384_2048();
    
    error_count += testMCHAN_LDST16384_1024();
    
    error_count += testMCHAN_LDST16384_512();
    
    error_count += testMCHAN_LDST16384_256();
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 80000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 10000000);
    
    error_count += testMCHAN_LDST16384_2048();
    
    error_count += testMCHAN_LDST16384_1024();
    
    error_count += testMCHAN_LDST16384_512();
    
    error_count += testMCHAN_LDST16384_256();
    
#endif
    
  }
  
  return error_count;
  
}

int testMCHAN_LDST16384_256(){
  
  volatile int i,j,id_tx, id_rx;
  volatile int test,read,error=0;
  
#ifdef VERBOSE
  printf ("STARTING TEST FOR 16 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",BUFFSIZE/16*4);
#endif
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  id_rx = mchan_alloc();
  
  id_tx = mchan_alloc();
  
  for (i=0;i<16;i++) {
    
    mchan_transfer(BUFFSIZE/16*4, RX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/16*4*i), (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/16*4*i), 0, 0, 0, 0);
    
  }
  
  for (i=0;i<16;i++) {
    
    mchan_transfer(BUFFSIZE/16*4, TX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/16*4*i), (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/16*4*i), 0, 0, 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  mchan_free(id_tx);
    
  for (i=0; i<BUFFSIZE; i++){
    
    test = 0xFF000000+i;
    read = *(int*)(TCDM_DATA_ADDR_2 + 4*i);
    
    if ( test != read ){
      printf("Error!!! RX Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  for (i=0; i<BUFFSIZE; i++){
    
    test = 0xFF000000+i;
    read = *(int*)(EXT_DATA_ADDR_2 + 4*i);
    
    if ( test != read ){
      printf("Error!!! TX Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  if (error == 0)
    printf("OOOOOOK!!!!!!\n");
  else
	printf("NOT OK!!!!!\n");
  
  return error;
  
}

int testMCHAN_LDST16384_512(){
  
  volatile int i,j,id_tx, id_rx;
  volatile int test,read,error=0;
  
  printf ("STARTING TEST FOR 8 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",BUFFSIZE/8*4);
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  id_rx = mchan_alloc();
  
  id_tx = mchan_alloc();
  
  for (i=0;i<8;i++) {
    
    mchan_transfer(BUFFSIZE/8*4, RX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/8*4*i) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/8*4*i), 0, 0, 0, 0);
    
  }
  
  for (i=0;i<8;i++) {
      
    mchan_transfer(BUFFSIZE/8*4, TX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/8*4*i) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/8*4*i), 0, 0, 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  mchan_free(id_tx);
  
  if (get_core_id() == 0){
    
    for (i=0; i<BUFFSIZE; i++){
      
      test = 0xFF000000+i;
      read = *(int*)(TCDM_DATA_ADDR_2 + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    for (i=0; i<BUFFSIZE; i++){
      
      test = 0xFF000000+i;
      read = *(int*)(EXT_DATA_ADDR_2 + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    if (error == 0)
      printf("OOOOOOK!!!!!!\n");
    else
      printf("NOT OK!!!!!\n");
  }
  
  return error;
  
}

int testMCHAN_LDST16384_1024(){
  
  volatile int i,j,id_tx,id_rx;
  volatile int test,read,error=0;
    
  printf ("STARTING TEST FOR 4 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",BUFFSIZE/4*4);
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  id_rx = mchan_alloc();
  
  id_tx = mchan_alloc();
  
  for (i=0;i<4;i++) {
    
    mchan_transfer(BUFFSIZE/4*4, RX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/4*4*i) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/4*4*i), 0, 0, 0, 0);
    
  }
  
  for (i=0;i<4;i++) {
    
    mchan_transfer(BUFFSIZE/4*4, TX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/4*4*i) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/4*4*i), 0, 0, 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  mchan_free(id_tx);
  
  for (i=0; i<BUFFSIZE; i++){
    
    test = 0xFF000000+i;
    read = *(int*)(TCDM_DATA_ADDR_2 + 4*i);
    
    if ( test != read ){
      printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  for (i=0; i<BUFFSIZE; i++){
    
    test = 0xFF000000+i;
    read = *(int*)(EXT_DATA_ADDR_2 + 4*i);
    
    if ( test != read ){
      printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  if (error == 0)
    printf("OOOOOOK!!!!!!\n");
  else
    printf("NOT OK!!!!!\n");
  
  return error;
  
}

int testMCHAN_LDST16384_2048(){
  
  volatile int i,j,id_tx,id_rx;
  volatile int test,read,error=0;
    
  printf ("STARTING TEST FOR 2 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",BUFFSIZE/2*4);
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  for (i=0; i<BUFFSIZE; i++){
    *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
  }
  
  id_rx = mchan_alloc();
  
  id_tx = mchan_alloc();
  
  for (i=0;i<2;i++) {
    
    mchan_transfer(BUFFSIZE/2*4, RX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/2*4*i) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/2*4*i), 0, 0, 0, 0);
    
  }
  
  for (i=0;i<2;i++) {
    
    mchan_transfer(BUFFSIZE/2*4, TX, INC, LIN, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/2*4*i) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/2*4*i), 0, 0, 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  mchan_free(id_tx);
  
  for (i=0; i<BUFFSIZE; i++){
    
    test = 0xFF000000+i;
    read = *(int*)(TCDM_DATA_ADDR_2 + 4*i);
    
    if ( test != read ){
      printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  for (i=0; i<BUFFSIZE; i++){
      
    test = 0xFF000000+i;
    read = *(int*)(EXT_DATA_ADDR_2 + 4*i);
      
    if ( test != read ){
      printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
      error++;
    }
    
  }
  
  if (error == 0)
    printf("OOOOOOK!!!!!!\n");
  else
    printf("NOT OK!!!!!\n");
  
  return error;
  
}
