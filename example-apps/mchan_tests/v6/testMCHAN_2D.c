#include <math.h>
#include "mchan_tests.h"
#include "pulp.h"

#define MAX_BUFFER_SIZE 0x4000

#define VERBOSE

static unsigned char *ext;
static unsigned char *loc;

#define EXT_DATA_ADDR  ((unsigned int)ext)
#define TCDM_DATA_ADDR ((unsigned int)loc)

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride);

int main()
{
  int   error_count = 0;
  
  if (rt_core_id() == 0)
  {
    if ((ext = rt_alloc(RT_ALLOC_L2_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1;
    if ((loc = rt_alloc(RT_ALLOC_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1;
  }

  if (get_core_id() == 0){

    for ( int i = 4; i < 128; i=2*i ) { // COUNT
      for ( int j = i; j < 128; j=2*j ) { // STRIDE
    	error_count += testMCHAN(i*i, RX, INC, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j);
      }
    }

    for ( int i = 4; i < 128; i=2*i ) { // COUNT
      for ( int j = i; j < 128; j=2*j) { // STRIDE
    	error_count += testMCHAN(i*i, TX, INC, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j);
      }
    }
    
#if defined(PMU_VERSION)
    SetFllSoCFrequency((unsigned int)10000000);
    SetFllClusterFrequency((unsigned int)80000000);
    
    for ( int i = 4; i < 128; i=2*i ) { // COUNT
      for ( int j = i; j < 128; j=2*j ) { // STRIDE
    	error_count += testMCHAN(i*i, RX, INC, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j);
      }
    }
    
    for ( int i = 4; i < 128; i=2*i ) { // COUNT
      for ( int j = i; j < 128; j=2*j) { // STRIDE
    	error_count += testMCHAN(i*i, TX, INC, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j);
      }
    }
    
    SetFllSoCFrequency((unsigned int)80000000);
    SetFllClusterFrequency((unsigned int)10000000);
    
    for ( int i = 4; i < 128; i=2*i ) { // COUNT
      for ( int j = i; j < 128; j=2*j ) { // STRIDE
    	error_count += testMCHAN(i*i, RX, INC, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j);
      }
    }
    
    for ( int i = 4; i < 128; i=2*i ) { // COUNT
      for ( int j = i; j < 128; j=2*j) { // STRIDE
    	error_count += testMCHAN(i*i, TX, INC, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j);
      }
    }
 #endif
    
  }
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride){
  
  volatile unsigned int i,j,id,k=0;
  volatile unsigned int test,read,error=0;
  
  if (type == RX){
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR RX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<count; i++){
      for (j=0; j<(count>>2); j++){
	*(unsigned int*)(EXT_DATA_ADDR + stride*i + 4*j) = 0xFF000000 + k++;
      }
    }
    
  } else {
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR TX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<len; i++){
      *(unsigned int*)(TCDM_DATA_ADDR + 4*i) = 0xFF000000 + i;
    }
    
  }
  
#ifdef VERBOSE
  printf("len: %d, count: %d, stride: %d\n",len, count, stride);
#endif
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd, ele, ile, ble, ext_addr, tcdm_addr, count, stride);
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  if (type == RX){
    
    for (i=0; i<(len>>2); i++){
      
      test = 0xFF000000 + i;
      read = *(unsigned int*)(TCDM_DATA_ADDR + 4*i);
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      
    }
    
  }else{
    
    for (i=0; i<count; i++){
      for (j=0; j<(count>>2); j++){
	
	test = 0xFF000000 + k++;
	read = *(unsigned int*)(EXT_DATA_ADDR + stride*i + 4*j);
	
	if ( test != read ){
	  printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	  error++;
	}
	
      }
      
    }
    
  }
  
  if (error == 0)
    printf("OOOOOOK!!!!!!\n");
  else
    printf("NOT OK!!!!!\n");
  
  return error;
  
}
