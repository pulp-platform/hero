#include <math.h>
#include "mchan_tests.h"
#include "pulp.h"

#define MAX_BUFFER_SIZE 0x4000

L2_DATA static unsigned char ext[MAX_BUFFER_SIZE];
L1_DATA static unsigned char loc[MAX_BUFFER_SIZE];

#define EXT_DATA_ADDR  ((unsigned int) ext)
#define TCDM_DATA_ADDR ((unsigned int) loc)

#define START_OFFSET 7
#define BURST_OFFSET 121

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride);

int main()
{

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);

  
  int error_count = 0;
  unsigned int i,j;
 

  if (get_core_id() == 0){
    
    for (i = 5; i < 64; i+=START_OFFSET){
      for (j = 17; j < 1024; j+=BURST_OFFSET){
	
	error_count += testMCHAN(j, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0, 0, 0);
	
	error_count += testMCHAN(j, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0, 0, 0);
	
      }
    }


#if defined(PMU_VERSION)
     rt_freq_set(RT_FREQ_DOMAIN_FC, 10000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 80000000);
    
    for (i = 5; i < 64; i+=START_OFFSET){
      for (j = 17; j < 1024; j+=BURST_OFFSET){
	
	error_count += testMCHAN(j, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0, 0, 0);
	
	error_count += testMCHAN(j, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0, 0, 0);
	
      }
    }
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 80000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 10000000);
    
    for (i = 5; i < 64; i+=START_OFFSET){
      for (j = 17; j < 1024; j+=BURST_OFFSET){
	
	error_count += testMCHAN(j, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0, 0, 0);
	
	error_count += testMCHAN(j, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR+i, TCDM_DATA_ADDR, 0, 0, 0, 0);
	
      }
    }
#endif
    
    print_summary(error_count);
   
    return error_count;
  }
  
  return 0;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride){
  
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
  
  mchan_transfer(len, type, incr, twd_ext, twd_tcdm, ele, ile, ble, ext_addr, tcdm_addr, ext_count, ext_stride, tcdm_count, tcdm_stride);
  
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
