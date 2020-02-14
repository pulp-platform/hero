//#include "mchan.h"
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE

static char *EXT_DATA_ADDR;
static char *TCDM_DATA_ADDR;

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride);

int main()
{
  
  int   error_count = 0;
  int i;
  
  if (rt_core_id() == 0)
  {
    if ((EXT_DATA_ADDR = rt_alloc(RT_ALLOC_L2_CL_DATA, 0x4000)) == 0) return -1;
    if ((TCDM_DATA_ADDR = rt_alloc(RT_ALLOC_CL_DATA, 0x4000)) == 0) return -1;
  }

  rt_team_barrier();
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, RX, INC, LIN, 1, 0, 0, (unsigned int) EXT_DATA_ADDR, (unsigned int) TCDM_DATA_ADDR, 0, 0);
  }
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, TX, INC, LIN, 1, 0, 0, (unsigned int) EXT_DATA_ADDR,  (unsigned int) TCDM_DATA_ADDR, 0, 0);
  }
  
  rt_team_barrier();
  
#if defined(PMU_VERSION)
  if (get_core_id() == 0){
    
    SetFllSoCFrequency((unsigned int)10000000);
    SetFllClusterFrequency((unsigned int)80000000);
    
  }
  
  rt_team_barrier();
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, RX, INC, LIN, 1, 0, 0, (unsigned int) EXT_DATA_ADDR, (unsigned int) TCDM_DATA_ADDR, 0, 0);
  }
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, TX, INC, LIN, 1, 0, 0, (unsigned int) EXT_DATA_ADDR,  (unsigned int) TCDM_DATA_ADDR, 0, 0);
  }
  
  rt_team_barrier();
  
  if (get_core_id() == 0){
    
    SetFllSoCFrequency((unsigned int)80000000);
    SetFllClusterFrequency((unsigned int)10000000);
    
  }
  
  rt_team_barrier();
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, RX, INC, LIN, 1, 0, 0, (unsigned int) EXT_DATA_ADDR, (unsigned int) TCDM_DATA_ADDR, 0, 0);
  }
  
  for (i=8; i<4096; i=i*2){
    error_count += testMCHAN(i, TX, INC, LIN, 1, 0, 0, (unsigned int) EXT_DATA_ADDR,  (unsigned int) TCDM_DATA_ADDR, 0, 0);
  }
  
  rt_team_barrier();
#endif
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride){
  
  volatile unsigned int i,j;
  int id;
  volatile int test,read,error=0;
  
  if (get_core_id() == 0){
    
    if (type == RX){
      
#ifdef VERBOSE
      printf ("STARTING TEST FOR RX %d  OPERATION: \n",len);
#endif
    
      for (i=0; i<len*rt_nb_pe()/4; i++){
	*(int*)(EXT_DATA_ADDR + 4*i) = 0xFF000000 + i;
      }
      
    } else {
      
#ifdef VERBOSE
      printf ("STARTING TEST FOR TX %d  OPERATION: \n",len);
#endif
    
      for (i=0; i<len*rt_nb_pe()/4; i++){
	*(int*)(TCDM_DATA_ADDR + 4*i) = 0xFF000000 + i;
      }
      
    }
    
  }
  
  rt_team_barrier();
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd, ele, ile, ble, ext_addr + len*get_core_id(), tcdm_addr + len*get_core_id(), 0,0);
  
  for (i=get_core_id(); i<len; i++){
    j = *(int*)(EXT_DATA_ADDR + 4*i);
  }
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  rt_team_barrier();
  
  if (get_core_id() == 0){
    
    if (type == RX){
      
      for (i=0; i<len*rt_nb_pe()/4; i++){
	
	test = 0xFF000000+i;
	read = *(int*)(TCDM_DATA_ADDR + 4*i);
	
	if ( test != read ){
	  printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	  error++;
	}
	
      }
      
    } else {
      
      for (i=0; i<len*rt_nb_pe()/4; i++){
	
	test = 0xFF000000+i;
	read = *(int*)(EXT_DATA_ADDR + 4*i);
	
	if ( test != read ){
	  printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	  error++;
	}
	
      }
      
    };
    
    if (error == 0)
      printf("OOOOOOK!!!!!!\n");
    else
      printf("NOT OK!!!!!\n");
    
  }
  
  rt_team_barrier();
  
  return error;
  
}
