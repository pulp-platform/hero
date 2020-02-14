#include <math.h>
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE

#define MAX_BUFFER_SIZE 0x37F0

static L1_DATA unsigned char loc[MAX_BUFFER_SIZE];
static L2_DATA unsigned char ext[MAX_BUFFER_SIZE];

#define EXT_DATA_ADDR  ((unsigned int)ext)
#define TCDM_DATA_ADDR ((unsigned int)loc)

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride);

int main()
{

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);

  
  int   error_count = 0;
  
  if (get_core_id() == 0){
    
    for ( int i = 4; i < 128; i=i+4) { // size
      for ( int j = 0; j < 16; j=j+4) { // base address
    	error_count += testMCHAN(i, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR + j, TCDM_DATA_ADDR, 0, 0, 0, 0);
      }
    }
    
    for ( int i = 4; i < 128; i=i+4) { //size
      for ( int j = 0; j < 16; j=j+4 ) { //base address
	error_count += testMCHAN(i, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR + j, TCDM_DATA_ADDR, 0, 0, 0, 0);
      }
    }
    
#if defined(PMU_VERSION)
     rt_freq_set(RT_FREQ_DOMAIN_FC, 10000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 80000000);
    
    for ( int i = 4; i < 128; i=i+4) { // size
      for ( int j = 0; j < 16; j=j+4) { // base address
    	error_count += testMCHAN(i, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR + j, TCDM_DATA_ADDR, 0, 0, 0, 0);
      }
    }
    
    for ( int i = 4; i < 128; i=i+4) { //size
      for ( int j = 0; j < 16; j=j+4 ) { //base address
	error_count += testMCHAN(i, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR + j, TCDM_DATA_ADDR, 0, 0, 0, 0);
      }
    }
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 80000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 10000000);
    
    for ( int i = 4; i < 128; i=i+4) { // size
      for ( int j = 0; j < 16; j=j+4) { // base address
    	error_count += testMCHAN(i, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR + j, TCDM_DATA_ADDR, 0, 0, 0, 0);
      }
    }
    
    for ( int i = 4; i < 128; i=i+4) { //size
      for ( int j = 0; j < 16; j=j+4 ) { //base address
	error_count += testMCHAN(i, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR + j, TCDM_DATA_ADDR, 0, 0, 0, 0);
      }
    }
    
#endif
  }
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride){
   
  volatile unsigned int i,j,id;
  volatile unsigned int test,read,error=0;
  
  if (type == RX){
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR RX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<len/4; i++){
      *(unsigned int*)(ext_addr + 4*i) = 0xFF000000 + 1024*len + i;
    }
    
    for (i=0; i<len/4+16; i++){
      *(unsigned int*)(tcdm_addr + 4*i) = 0;
    }
    
  } else {
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR TX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<len/4; i++){
      *(unsigned int*)(tcdm_addr + 4*i) = 0xFF000000 + 1024*len + i;
    }
    
    for (i=0; i<len/4+16; i++){
      *(unsigned int*)(ext_addr+ 4*i) = 0;
    }
    
  }
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd_ext, twd_tcdm, ele, ile, ble, ext_addr, tcdm_addr, ext_count, ext_stride, tcdm_count, tcdm_stride);
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  if (type == RX){
    
    for (i=0; i<len/4; i++){
      
      test = 0xFF000000 + 1024*len + i;
      read = *(unsigned int*)(tcdm_addr + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    for (i=len; i<len/4+16; i++){
      
      test = 0;
      read = *(unsigned int*)(tcdm_addr + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
  }else{
    
    for (i=0; i<len/4; i++){
      
      test = 0xFF000000 + 1024*len+i;
      read = *(unsigned int*)(ext_addr + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
    for (i=len; i<len/4+16; i++){
      
      test = 0;
      read = *(unsigned int*)(ext_addr + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
  }
  
  if (error == 0)
    printf("OOOOOOK!!!!!!\n");
  else
    printf("NOT OK!!!!!\n");
  
  return error;
  
}
