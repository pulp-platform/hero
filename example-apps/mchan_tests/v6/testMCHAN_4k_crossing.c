#include <math.h>
#include "mchan_tests.h"
#include "pulp.h"

#define MAX_BUFFER_SIZE 0x4000

static char *EXT_DATA_ADDR;
static char *TCDM_DATA_ADDR;

#define START_OFFSET 7
#define BURST_OFFSET 121

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride);

int main()
{
  int error_count = 0;
  unsigned int i,j;
  
  if (rt_core_id() == 0)
  {
    if ((EXT_DATA_ADDR = rt_alloc(RT_ALLOC_L2_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1;
    if ((TCDM_DATA_ADDR = rt_alloc(RT_ALLOC_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1;
  }

  if (get_core_id() == 0){
    
    for (i = 5; i < 64; i+=START_OFFSET){
      for (j = 17; j < 1024; j+=BURST_OFFSET){
	
	error_count += testMCHAN(j, RX, INC, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0);
	
	error_count += testMCHAN(j, TX, INC, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0);
	
      }
    }


#if defined(PMU_VERSION)
    SetFllSoCFrequency((unsigned int)10000000);
    SetFllClusterFrequency((unsigned int)80000000);
    
    for (i = 5; i < 64; i+=START_OFFSET){
      for (j = 17; j < 1024; j+=BURST_OFFSET){
	
	error_count += testMCHAN(j, RX, INC, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0);
	
	error_count += testMCHAN(j, TX, INC, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0);
	
      }
    }
    
    SetFllSoCFrequency((unsigned int)80000000);
    SetFllClusterFrequency((unsigned int)10000000);
    
    for (i = 5; i < 64; i+=START_OFFSET){
      for (j = 17; j < 1024; j+=BURST_OFFSET){
	
	error_count += testMCHAN(j, RX, INC, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0);
	
	error_count += testMCHAN(j, TX, INC, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0);
	
      }
    }
#endif
    
    print_summary(error_count);
   
    return error_count;
  }
  
  return 0;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride){
  
  volatile unsigned int i,j,id;
  volatile unsigned int test,read,error=0;
  
  if (type == RX){
    
    printf ("STARTING TEST FOR RX %d OPERATION, START ADDRESS %x : \n", len, ext_addr);
    
    for (i=0; i<len; i++){
      *(unsigned char*)(ext_addr + i) = i & 0xFF;
    }
    
    for (i=0; i<len+16; i++){
      *(unsigned char*)(tcdm_addr + i) = 0;
    }
    
  } else {
    
    printf ("STARTING TEST FOR TX %d OPERATION: \n", len);
    
    for (i=0; i<len; i++){
      *(unsigned char*)(tcdm_addr + i) = i & 0xFF;
    }
    
    for (i=0; i<len+16; i++){
      *(unsigned char*)(ext_addr + i) = 0;
    }
    
  }
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd, ele, ile, ble, ext_addr, tcdm_addr, 0, 0);
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  if (type == RX){
    
    for (i=0; i<len; i++){
      
      test = i & 0xFF;
      read = *(unsigned char*)(tcdm_addr + i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    for (i=len; i<len+16; i++){
      
      test = 0;
      read = *(unsigned char*)(tcdm_addr + i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
  }else{
    
    for (i=0; i<len; i++){
      
      test = i & 0xFF;
      read = *(unsigned char*)(ext_addr + i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    for (i=len; i<len+16; i++){
      
      test = 0;
      read = *(unsigned char*)(ext_addr + i);
      
      if ( test != read ){
	//printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
  }
  
  if (error == 0)
    printf("OK\n");
  else
    printf("NOT OK\n");
  
  return error;
  
}
