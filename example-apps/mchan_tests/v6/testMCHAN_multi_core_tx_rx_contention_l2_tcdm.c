//#include "mchan.h"
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE

static char *EXT_DATA_SRC_ADDR;
static char *TCDM_DATA_SRC_ADDR;
static char *EXT_DATA_DST_ADDR;
static char *TCDM_DATA_DST_ADDR;

int testMCHAN(unsigned int len, char incr, char twd, unsigned short int count, unsigned short int stride);

int main()
{
  
  int   i,error_count = 0;
  
  if (rt_core_id() == 0)
  {
    if ((EXT_DATA_SRC_ADDR = rt_alloc(RT_ALLOC_L2_CL_DATA, 0x4000)) == 0) return -1;
    if ((TCDM_DATA_SRC_ADDR = rt_alloc(RT_ALLOC_CL_DATA, 0x4000)) == 0) return -1;
    if ((EXT_DATA_DST_ADDR = rt_alloc(RT_ALLOC_L2_CL_DATA, 0x4000)) == 0) return -1;
    if ((TCDM_DATA_DST_ADDR = rt_alloc(RT_ALLOC_CL_DATA, 0x4000)) == 0) return -1;
  }

  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, INC, LIN, 0, 0);
  }
  
  rt_team_barrier();
  
#if defined(PMU_VERSION)
  if (get_core_id() == 0){
    
    SetFllSoCFrequency((unsigned int)10000000);
    SetFllClusterFrequency((unsigned int)80000000);
    
  }
  
  rt_team_barrier();
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, INC, LIN, 0, 0);
  }
  
  rt_team_barrier();
  
  if (get_core_id() == 0){
    
    SetFllSoCFrequency((unsigned int)80000000);
    SetFllClusterFrequency((unsigned int)10000000);
    
  }
  
  rt_team_barrier();
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, INC, LIN, 0, 0);
  }
  
  rt_team_barrier();
#endif
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char incr, char twd, unsigned short int count, unsigned short int stride){
  
  volatile unsigned int i,j,id1,id2;
  volatile int test,read,error=0;
  
  if (get_core_id() == 0){
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR %d TX AND RX CONCURRENT OPERATIONS: \n",len);
#endif
    
    for (i=0; i<len*rt_nb_pe()/4; i++){
      *(int*)(EXT_DATA_SRC_ADDR + 4*i) = 0xFF000000 + i;
    }
    
    for (i=0; i<len*rt_nb_pe()/4; i++){
      *(int*)(TCDM_DATA_SRC_ADDR + 4*i) = 0xFF010000 + i;
    }
    
  }
  
  rt_team_barrier();
  
  id1 = mchan_alloc();
  
  mchan_transfer(len, RX, incr, twd, 1, 0, 0, (unsigned int)(EXT_DATA_SRC_ADDR + len*get_core_id()), (unsigned int)(TCDM_DATA_DST_ADDR + len*get_core_id()), 0,0);
  
  id2 = mchan_alloc();
  
  mchan_transfer(len, TX, incr, twd, 1, 0, 0, (unsigned int)(EXT_DATA_DST_ADDR + len*get_core_id()), (unsigned int)(TCDM_DATA_SRC_ADDR + len*get_core_id()), 0 ,0);
  
  for (i=get_core_id(); i<len; i++){
    j= *(int*)(TCDM_DATA_SRC_ADDR + 4*i);
    j= *(int*)(EXT_DATA_SRC_ADDR + 4*i);
  }
  
  mchan_barrier(id1);
  mchan_barrier(id2);
  
  mchan_free(id1);
  mchan_free(id2);
  
  rt_team_barrier();
  
  if (get_core_id() == 0){
    
    for (i=0; i<len*rt_nb_pe()/4; i++){
      
      test = 0xFF000000+i;
      read = *(int*)(TCDM_DATA_DST_ADDR + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    for (i=0; i<len*rt_nb_pe()/4; i++){
      
      test = 0xFF010000+i;
      read = *(int*)(EXT_DATA_DST_ADDR + 4*i);
      
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
