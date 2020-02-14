//#include "mchan.h"
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE


//#if !defined(ARCHI_L1_SIZE) || ARCHI_L1_SIZE >= 65536
#define BUFFSIZE_BYTE 0x4000
#define BUFFSIZE (BUFFSIZE_BYTE/4)
//#else
//#define BUFFSIZE 0x2000
//#endif


static char *EXT_DATA_ADDR_1;
static char *EXT_DATA_ADDR_2;
static char *TCDM_DATA_ADDR_1;
static char *TCDM_DATA_ADDR_2;

int testMCHAN_LD16384();
int testMCHAN_ST16384();
int testMCHAN_LDST16384_256();
int testMCHAN_LDST16384_512();
int testMCHAN_LDST16384_1024();
int testMCHAN_LDST16384_2048();

int main()
{
  
  int   error_count = 0;
  
  if (rt_core_id() == 0)
  {
    if ((EXT_DATA_ADDR_1 = rt_alloc(RT_ALLOC_L2_CL_DATA, BUFFSIZE_BYTE)) == 0) return -1;
    if ((TCDM_DATA_ADDR_1 = rt_alloc(RT_ALLOC_CL_DATA, BUFFSIZE_BYTE)) == 0) return -1;
    if ((EXT_DATA_ADDR_2 = rt_alloc(RT_ALLOC_L2_CL_DATA, BUFFSIZE_BYTE)) == 0) return -1;
    if ((TCDM_DATA_ADDR_2 = rt_alloc(RT_ALLOC_CL_DATA, BUFFSIZE_BYTE)) == 0) return -1;
  }

  error_count += testMCHAN_LDST16384_2048();

  error_count += testMCHAN_LDST16384_1024();

  error_count += testMCHAN_LDST16384_512();
  
  error_count += testMCHAN_LDST16384_256();

  rt_team_barrier();
  
#if defined(PMU_VERSION)
  if (get_core_id() == 0){
    
    SetFllSoCFrequency((unsigned int)10000000);
    SetFllClusterFrequency((unsigned int)80000000);
    
  }
  
  rt_team_barrier();
  
  error_count += testMCHAN_LDST16384_2048();
  
  error_count += testMCHAN_LDST16384_1024();
  
  error_count += testMCHAN_LDST16384_512();
  
  error_count += testMCHAN_LDST16384_256();
  
  rt_team_barrier();
  
  if (get_core_id() == 0){
    
    SetFllSoCFrequency((unsigned int)80000000);
    SetFllClusterFrequency((unsigned int)10000000);
    
  }
  
  rt_team_barrier();
  
  error_count += testMCHAN_LDST16384_2048();
  
  error_count += testMCHAN_LDST16384_1024();
  
  error_count += testMCHAN_LDST16384_512();
  
  error_count += testMCHAN_LDST16384_256();
  
  rt_team_barrier();
#endif
  
  return error_count;
  
}

int testMCHAN_LDST16384_256(){
  
  volatile int i,j,id_tx, id_rx;
  volatile int test,read,error=0;
  
  if (get_core_id() == 0){
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR %d X 16 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",rt_nb_pe(),BUFFSIZE/16*4/rt_nb_pe());
#endif
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
  }
  
  rt_team_barrier();
  
  id_rx = mchan_alloc();
  
  //id_tx = mchan_alloc();
  
  for (i=0;i<16;i++) {
    
    mchan_transfer(BUFFSIZE/16*4/rt_nb_pe(), RX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/16*4*get_core_id()/rt_nb_pe() + BUFFSIZE/16*4*rt_nb_pe()*i/rt_nb_pe()) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/16*4/rt_nb_pe()*get_core_id() + BUFFSIZE/16*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  for (i=0;i<16;i++) {
    
    mchan_transfer(BUFFSIZE/16*4/rt_nb_pe(), TX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/16*4*get_core_id()/rt_nb_pe() + BUFFSIZE/16*4*rt_nb_pe()*i/rt_nb_pe()) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/16*4*get_core_id()/rt_nb_pe() + BUFFSIZE/16*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  //mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  //mchan_free(id_tx);
  
  rt_team_barrier();
  
  if (get_core_id() == 0){
    
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
  }
  
  rt_team_barrier();
  
  return error;
  
}

int testMCHAN_LDST16384_512(){
  
  volatile int i,j,id_tx, id_rx;
  volatile int test,read,error=0;
  
  if (get_core_id() == 0){
    
    printf ("STARTING TEST FOR %d X 8 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",rt_nb_pe(),BUFFSIZE/8*4/rt_nb_pe());
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
  }
  
  rt_team_barrier();
  
  id_rx = mchan_alloc();
  
  //id_tx = mchan_alloc();
  
  for (i=0;i<8;i++) {
    
    mchan_transfer(BUFFSIZE/8*4/rt_nb_pe(), RX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/8*4*get_core_id()/rt_nb_pe() + BUFFSIZE/8*4*rt_nb_pe()*i/rt_nb_pe()) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/8*4*get_core_id()/rt_nb_pe() + BUFFSIZE/8*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  for (i=0;i<8;i++) {
      
    mchan_transfer(BUFFSIZE/8*4/rt_nb_pe(), TX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/8*4*get_core_id()/rt_nb_pe() + BUFFSIZE/8*4*rt_nb_pe()*i/rt_nb_pe()) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/8*4*get_core_id()/rt_nb_pe() + BUFFSIZE/8*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  //mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  //mchan_free(id_tx);
  
  rt_team_barrier();
  
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
  
  rt_team_barrier();
  
  return error;
  
}

int testMCHAN_LDST16384_1024(){
  
  volatile int i,j,id_tx,id_rx;
  volatile int test,read,error=0;
  
  if (get_core_id() == 0){
    
    printf ("STARTING TEST FOR %d X 4 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",rt_nb_pe(),BUFFSIZE/4*4/rt_nb_pe());
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
  }
  
  rt_team_barrier();
  
  id_rx = mchan_alloc();
  
  //id_tx = mchan_alloc();
  
  for (i=0;i<4;i++) {
    
    mchan_transfer(BUFFSIZE/4*4/rt_nb_pe(), RX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/4*4/rt_nb_pe()*get_core_id() + BUFFSIZE/4*4*rt_nb_pe()*i/rt_nb_pe()) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/4*4*get_core_id()/rt_nb_pe() + BUFFSIZE/4*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  for (i=0;i<4;i++) {
    
    mchan_transfer(BUFFSIZE/4*4/rt_nb_pe(), TX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/4*4/rt_nb_pe()*get_core_id() + BUFFSIZE/4*4/rt_nb_pe()*rt_nb_pe()*i) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/4*4*get_core_id()/rt_nb_pe() + BUFFSIZE/4*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  mchan_barrier(id_rx);
  
  //mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  //mchan_free(id_tx);
  
  rt_team_barrier();
  
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
  
  rt_team_barrier();
  
  return error;
  
}

int testMCHAN_LDST16384_2048(){
  
  volatile int i,j,id_tx,id_rx;
  volatile int test,read,error=0;
  
  if (get_core_id() == 0){
    
    printf ("STARTING TEST FOR %d X 2 X %d CONCURRENT LOAD AND STORE OPERATIONS: \n",rt_nb_pe(),BUFFSIZE/2*4/rt_nb_pe());
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(TCDM_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
    for (i=0; i<BUFFSIZE; i++){
      *(int*)(EXT_DATA_ADDR_1 + 4*i) = 0xFF000000 + i;
    }
    
  }
  
  rt_team_barrier();
  
  id_rx = mchan_alloc();
  
  //id_tx = mchan_alloc();
  
  for (i=0;i<2;i++) {
    
    mchan_transfer(BUFFSIZE/2*4/rt_nb_pe(), RX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_1 + BUFFSIZE/2*4*get_core_id()/rt_nb_pe() + BUFFSIZE/2*4*rt_nb_pe()*i/rt_nb_pe()) , (int)(TCDM_DATA_ADDR_2 + BUFFSIZE/2*4*get_core_id()/rt_nb_pe() + BUFFSIZE/2*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }
  
  for (i=0;i<2;i++) {
    
    mchan_transfer(BUFFSIZE/2*4/rt_nb_pe(), TX, INC, LIN, 1, 0, 0, (int)(EXT_DATA_ADDR_2 + BUFFSIZE/2*4*get_core_id()/rt_nb_pe() + BUFFSIZE/2*4/rt_nb_pe()*rt_nb_pe()*i) , (int)(TCDM_DATA_ADDR_1 + BUFFSIZE/2*4*get_core_id()/rt_nb_pe() + BUFFSIZE/2*4*rt_nb_pe()*i/rt_nb_pe()), 0, 0);
    
  }

  mchan_barrier(id_rx);
  
  //mchan_barrier(id_tx);
  
  mchan_free(id_rx);
  
  //mchan_free(id_tx);
  
  rt_team_barrier();
  
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
  
  rt_team_barrier();
  
  return error;
  
}
