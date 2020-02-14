#include <math.h>
#include "pulp.h"
#include "mchan_tests.h"

#define VERBOSE

#define MAX_BUFFER_SIZE 0x4000

L2_DATA static unsigned char ext[MAX_BUFFER_SIZE];
L1_DATA static unsigned char loc[MAX_BUFFER_SIZE];

#define EXT_DATA_ADDR  ((unsigned int)ext)
#define TCDM_DATA_ADDR ((unsigned int)loc)

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride);

int main()
{

  if (rt_cluster_id() != 0)
    return bench_cluster_forward(0);
  
  int   i, error_count = 0;
  


  if (get_core_id() == 0){
    
    // FIFO WIDTH = 1 BYTE
    for ( i = 1; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 1, 0);
    }
    
    // FIFO WIDTH = 1 BYTE
    for ( i = 1; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 1, 0);
    }
    
    // FIFO WIDTH = 2 BYTES
    for ( i = 2; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 2, 0);
    }
    
    // FIFO WIDTH = 2 BYTES
    for ( i = 2; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 2, 0);
    }
    
    // FIFO WIDTH = 4 BYTES
    for ( i = 4; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 4, 0);
    }
    
    // FIFO WIDTH = 4 BYTES
    for ( i = 4; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 4, 0);
    }
    
    // FIFO WIDTH = 8 BYTES
    for ( i = 8; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 8, 0);
    }
    
    // FIFO WIDTH = 8 BYTES
    for ( i = 8; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 8, 0);
    }
    
#if defined(PMU_VERSION)
     rt_freq_set(RT_FREQ_DOMAIN_FC, 10000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 80000000);
    
    // FIFO WIDTH = 1 BYTE
    for ( i = 1; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 1, 0);
    }
    
    // FIFO WIDTH = 1 BYTE
    for ( i = 1; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 1, 0);
    }
    
    // FIFO WIDTH = 2 BYTES
    for ( i = 2; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 2, 0);
    }
    
    // FIFO WIDTH = 2 BYTES
    for ( i = 2; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 2, 0);
    }
    
    // FIFO WIDTH = 4 BYTES
    for ( i = 4; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 4, 0);
    }
    
    // FIFO WIDTH = 4 BYTES
    for ( i = 4; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 4, 0);
    }
    
    // FIFO WIDTH = 8 BYTES
    for ( i = 8; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 8, 0);
    }
    
    // FIFO WIDTH = 8 BYTES
    for ( i = 8; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 8, 0);
    }
    
     rt_freq_set(RT_FREQ_DOMAIN_FC, 80000000);
     rt_freq_set(RT_FREQ_DOMAIN_CL, 10000000);
    
    // FIFO WIDTH = 1 BYTE
    for ( i = 1; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 1, 0);
    }
    
    // FIFO WIDTH = 1 BYTE
    for ( i = 1; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 1, 0);
    }
    
    // FIFO WIDTH = 2 BYTES
    for ( i = 2; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 2, 0);
    }
    
    // FIFO WIDTH = 2 BYTES
    for ( i = 2; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 2, 0);
    }
    
    // FIFO WIDTH = 4 BYTES
    for ( i = 4; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 4, 0);
    }
    
    // FIFO WIDTH = 4 BYTES
    for ( i = 4; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 4, 0);
    }
    
    // FIFO WIDTH = 8 BYTES
    for ( i = 8; i < 2048; i=2*i ) {
      error_count += testMCHAN(i, RX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 8, 0);
    }
    
    // FIFO WIDTH = 8 BYTES
    for ( i = 8; i < 2048; i=2*i) {
      error_count += testMCHAN(i, TX, FIX, TWD, 1, 0, 0, EXT_DATA_ADDR, TCDM_DATA_ADDR, 8, 0);
    }
#endif
    
  }
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride){
  
  volatile unsigned int i,j,id;
  volatile unsigned int test,read,test1,read1,test2,read2,error=0;
  
  if (type == RX){
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR RX %d OPERATIONS, FIFO WIDTH = %d BYTES: \n", len, count);
#endif
    
    *(unsigned int*)(ext_addr)    = 0x76543210;
    *(unsigned int*)(ext_addr+4)  = 0xFEDCBA98;
    
  } else {
    
#ifdef VERBOSE
    printf ("STARTING TEST FOR TX %d OPERATION, FIFO WIDTH = %d BYTES: \n", len, count);
#endif
    
    switch (count){
      
    case 1:
      
      for (i=0; i<len; i++){
	*(unsigned int*)(tcdm_addr + i) = len & 0xFF;
      }
      
      *(unsigned int*)(ext_addr) = 0;
      break;
      
    case 2:
      
      for (i=0; i<len; i+=2){
	*(unsigned int*)(tcdm_addr + i) = len & 0xFFFF;
      }
      
      *(unsigned int*)(ext_addr) = 0;
      break;
      
    case 4:
      
      for (i=0; i<len; i+=4){
	*(unsigned int*)(tcdm_addr + i) = len & 0xFFFFFFFF;
      }
      
      *(unsigned int*)(ext_addr) = 0;
      break;
      
    case 8:
      
      for (i=0; i<len; i+=8){
	*(unsigned int*)(tcdm_addr + i)    = len & 0xFFFFFFFF;
	*(unsigned int*)(tcdm_addr + 4 +i) = (0x1000 + len) & 0xFFFFFFFF;
      }
      
      *(unsigned int*)(ext_addr) = 0;
      break;
      
    default:
      break;
      
    }
    
  }
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd, 0, ele, ile, ble, ext_addr, tcdm_addr, count, 0, 0, 0);
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  if (type == RX){
    
    switch (count){
      
    case 1:
      
      for (i=0; i<len; i+=1){
	
	test1 = 0x10;
	read1 = *(unsigned int*)(tcdm_addr + i) & 0xFF;
	
	if (test1 != read1){
	  printf("Error!!! Read: %x, Test: %x, Index: %d \n ",read1,test1,i);
	  error++;
	}
	
      }
      break;
      
    case 2:
      for (i=0; i<len; i+=2){
	
	test1 = 0x3210;
	read1 = *(unsigned int*)(tcdm_addr + i) & 0xFFFF;
	
	if (test1 != read1){
	  printf("Error!!! Read: %x, Test: %x, Index: %d \n ",read1,test1,i);
	  error++;
	}
	
      }
      break;
      
    case 4:
      for (i=0; i<len; i+=4){
	
	test1 = 0x76543210;
	read1 = *(unsigned int*)(tcdm_addr + i);
	
	if (test1 != read1){
	  printf("Error!!! Read: %x, Test: %x, Index: %d \n ",read1,test1,i);
	  error++;
	}
	
      }
      break;
      
    case 8:
      
      for (i=0; i<len; i+=8){
	
	test1 = 0x76543210;
	read1 = *(unsigned int*)(tcdm_addr + i);
	test2 = 0xFEDCBA98;
	read2 = *(unsigned int*)(tcdm_addr + 4 + i);
	
	if ( (test1 != read1) || (test2 != read2) ){
	  printf("Error!!! Read: %x, Test:%x, Read: %x, Test:%x, Index: %d \n ",read1,test1,read2,test2,i);
	  error++;
	}
	
      }
      break;
      
    default:
      break;
      
    }
    
  }else{
    
    switch (count){
      
    case 1:
      
      test = len & 0xFF;
      read = *(unsigned int*)(ext_addr) & 0xFF;
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
       }
      break;
      
    case 2:
      
      test = len & 0xFFFF;
      read = *(unsigned int*)(ext_addr) & 0xFFFF;
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      break;
      
    case 4:
      
      test = len & 0xFFFFFFFF;
      read = *(unsigned int*)(ext_addr) & 0xFFFFFFFF;
      
      if ( test != read ){
	printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
	error++;
      }
      break;
      
    case 8:
      test1 = len & 0xFFFFFFFF;
      test2 = (len + 0x1000) & 0xFFFFFFFF;
      read1 = *(unsigned int*)(ext_addr) & 0xFFFFFFFF;
      read2 = *(unsigned int*)(ext_addr + 4) & 0xFFFFFFFF;
      
      if ( test1 != read1 | test2 != read2 ){
	printf("Error!!! Read: %x, Test:%x, Read: %x, Test:%x, Index: %d \n ",read1,test1,read2,test2,i);
	error++;
      }
      break;
      
    default:
      break;
      
    }
    
  }
  
  if (error == 0)
    printf("OOOOOOK!!!!!!\n");
  else
    printf("NOT OK!!!!!\n");
  
  return error;
  
}
