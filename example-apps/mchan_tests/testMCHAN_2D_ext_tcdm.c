#include <math.h>
#include "mchan_tests.h"
#include "pulp.h"

#define MAX_EXT_BUFFER_SIZE  0x8000
#define MAX_TCDM_BUFFER_SIZE 0x8000

#define VERBOSE

L2_DATA static unsigned char ext[MAX_EXT_BUFFER_SIZE];
L1_DATA static unsigned char loc[MAX_TCDM_BUFFER_SIZE];

#define EXT_DATA_ADDR  ((unsigned int)ext)
#define TCDM_DATA_ADDR ((unsigned int)loc)

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride);

int main()
{

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);
  
  int   error_count = 0;
  
  
  if (get_core_id() == 0){
    
    for ( int i = 4; i < 64; i=2*i ) { // EXT COUNT
      for ( int j = i; j < 64; j=2*j ) { // EXT STRIDE
	for ( int k = 4; k < 64; k=2*k ) { // TCDM COUNT
	  for ( int l = k; l < 64; l=2*l ) { // TCDM STRIDE
	    error_count += testMCHAN(i*i, RX, INC, TWD, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j, k, l);
	  }
	}
      }
    }
    
    for ( int i = 4; i < 64; i=2*i ) { // EXT COUNT
      for ( int j = i; j < 64; j=2*j ) { // EXT STRIDE
	for ( int k = 4; k < 64; k=2*k ) { // TCDM COUNT
	  for ( int l = k; l < 64; l=2*l ) { // TCDM STRIDE
	    error_count += testMCHAN(i*i, TX, INC, TWD, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j, k, l);
	  }
	}
      }
    }
    
#if defined(PMU_VERSION)
    rt_freq_set(RT_FREQ_DOMAIN_FC, 10000000);
    rt_freq_set(RT_FREQ_DOMAIN_CL, 80000000);

    for ( int i = 4; i < 64; i=2*i ) { // EXT COUNT
      for ( int j = i; j < 64; j=2*j ) { // EXT STRIDE
	for ( int k = 4; k < 64; k=2*k ) { // TCDM COUNT
	  for ( int l = k; l < 64; l=2*l ) { // TCDM STRIDE
	    error_count += testMCHAN(i*i, RX, INC, TWD, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j, k, l);
	  }
	}
      }
    }
    
    for ( int i = 4; i < 64; i=2*i ) { // EXT COUNT
      for ( int j = i; j < 64; j=2*j ) { // EXT STRIDE
	for ( int k = 4; k < 64; k=2*k ) { // TCDM COUNT
	  for ( int l = k; l < 64; l=2*l ) { // TCDM STRIDE
	    error_count += testMCHAN(i*i, TX, INC, TWD, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j, k, l);
	  }
	}
      }
    }
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 80000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 10000000);
    
    for ( int i = 4; i < 64; i=2*i ) { // EXT COUNT
      for ( int j = i; j < 64; j=2*j ) { // EXT STRIDE
	for ( int k = 4; k < 64; k=2*k ) { // TCDM COUNT
	  for ( int l = k; l < 64; l=2*l ) { // TCDM STRIDE
	    error_count += testMCHAN(i*i, RX, INC, TWD, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j, k, l);
	  }
	}
      }
    }
    
    for ( int i = 4; i < 64; i=2*i ) { // EXT COUNT
      for ( int j = i; j < 64; j=2*j ) { // EXT STRIDE
	for ( int k = 4; k < 64; k=2*k ) { // TCDM COUNT
	  for ( int l = k; l < 64; l=2*l ) { // TCDM STRIDE
	    error_count += testMCHAN(i*i, TX, INC, TWD, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, i, j, k, l);
	  }
	}
      }
    }
    
#endif
    
  }
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride){
  
  volatile unsigned int i,j,id;
  volatile unsigned char test,read,error=0,k=0;
  
  if (type == RX){
    
    k=0;
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR RX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<len/ext_count; i++){
      for (j=0; j<ext_count; j++){
	*(unsigned char*)(EXT_DATA_ADDR + ext_stride*i + j) = k++;
      }
    }
    
  } else {
    
    k=0;
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR TX %d OPERATION: \n", len);
#endif
    
    for (i=0; i<len/tcdm_count; i++){
      for (j=0; j<tcdm_count; j++){
	*(unsigned char*)(TCDM_DATA_ADDR + tcdm_stride*i + j) = k++;
      }
    }
    
  }
  
#ifdef VERBOSE
  printf("len: %d, ext_count: %d, ext_stride: %d, tcdm_count: %d, tcdm_stride: %d\n",len, ext_count, ext_stride, tcdm_count, tcdm_stride);
#endif
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd_ext, twd_tcdm, ele, ile, ble, ext_addr, tcdm_addr, ext_count, ext_stride, tcdm_count, tcdm_stride);
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  if (type == RX){
    
    k=0;
    
    for (i=0; i<len/tcdm_count; i++){
      for (j=0; j<tcdm_count; j++){
	
	test = k++;
	read = *(unsigned char*)(TCDM_DATA_ADDR + tcdm_stride*i + j);
	
	if ( test != read ){
	  printf("Error!!! Read: %x, Test:%x, Index: %d, %d, Addr: %x  \n ",read,test,i,j,(TCDM_DATA_ADDR + tcdm_stride*i + j));
	  error++;
	}
	
      }
      
    }
    
  }else{
    
    k=0;
    
    for (i=0; i<len/ext_count; i++){
      for (j=0; j<ext_count; j++){
	
	test = k++;
	read = *(unsigned char*)(EXT_DATA_ADDR + ext_stride*i + j);
	
	if ( test != read ){
	  printf("Error!!! Read: %x, Test:%x, Index: %d, %d \n ",read,test,i,j);
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
