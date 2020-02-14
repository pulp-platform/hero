#include <math.h>
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE

#define MAX_BUFFER_SIZE 0x4000

//static unsigned char *ext;
//static unsigned char *loc;

//#define EXT_DATA_ADDR  ((unsigned int)ext)
//#define TCDM_DATA_ADDR ((unsigned int)loc)

L2_DATA static unsigned char ext[MAX_BUFFER_SIZE];
L1_DATA static unsigned char loc[MAX_BUFFER_SIZE];

#define EXT_DATA_ADDR  ((unsigned int) ext)
#define TCDM_DATA_ADDR ((unsigned int) loc)

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride);

int main()
{

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);

  
  int   error_count = 0;
  
  
 /*  if (rt_core_id() == 0) */
/*   { */
/*     if ((ext = rt_alloc(RT_ALLOC_L2_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1; */
/*     if ((loc = rt_alloc(RT_ALLOC_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1; */
/*   } */

  if (get_core_id() == 0){


    for ( int i = 1; i < 16384; i=2*i) {
      error_count += testMCHAN(i, TX, INC, LIN, LIN, 1, 0, 0,  ((unsigned int) ext), TCDM_DATA_ADDR, 0, 0, 0, 0);
    } 
    for ( int i = 1; i < 16384; i=2*i ) {
      error_count += testMCHAN(i, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 0, 0, 0, 0);
    }
    
#if defined(PMU_VERSION)
     rt_freq_set(RT_FREQ_DOMAIN_FC, 10000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 80000000);
    
    for ( int i = 1; i < 16384; i=2*i) {
      error_count += testMCHAN(i, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 0, 0, 0, 0);
    } 
    for ( int i = 1; i < 16384; i=2*i ) {
      error_count += testMCHAN(i, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 0, 0, 0, 0);
    }
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 80000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 10000000);
        
    for ( int i = 1; i < 16384; i=2*i) {
      error_count += testMCHAN(i, TX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 0, 0, 0, 0);
    } 
    for ( int i = 1; i < 16384; i=2*i ) {
      error_count += testMCHAN(i, RX, INC, LIN, LIN, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 0, 0, 0, 0);
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
    
    for (i=0; i<len; i++){
      *(unsigned char*)(ext_addr + i) = i & 0xFF;
    }
    
    for (i=0; i<len+16; i++){
      *(unsigned char*)(tcdm_addr + i) = 0;
    }
    
  } else {
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR TX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<len; i++){
      *(unsigned char*)(tcdm_addr + i) = i & 0xFF;
    }
    
    for (i=0; i<len+16; i++){
      *(unsigned char*)(ext_addr+ i) = 0;
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
