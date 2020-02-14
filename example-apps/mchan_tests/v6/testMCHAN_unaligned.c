#include <math.h>
//#include "mchan.h"
#include "pulp.h"
#include "mchan_tests.h"

#define MAX_BUFFER_SIZE 0x4000

static unsigned char *ext;
static unsigned char *loc;

#define EXT_DATA_ADDR  ((unsigned int)ext)
#define TCDM_DATA_ADDR ((unsigned int)loc)

int testMCHAN(unsigned int len, char type, char incr, char twd, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride );

int main()
{
  
  int   error_count = 0;
  int i,j,k,l;
  
  if (rt_core_id() == 0)
  {
    if ((ext = rt_alloc(RT_ALLOC_L2_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1;
    if ((loc = rt_alloc(RT_ALLOC_CL_DATA, MAX_BUFFER_SIZE)) == 0) return -1;
  }

  if (get_core_id() == 0){
    for (i=1; i<32; i++) { // SIZE
      for (j=0; j<8; j++) { // TCDM ADDR
        for (k=0; k<8; k++) { // EXT ADDR
          for (l=0; l<2; l++) { // TYPE
            error_count += testMCHAN(i,l,INC,LIN,EXT_DATA_ADDR+k,TCDM_DATA_ADDR+j,0,0);
          }
        }
      }
    }
    
#if defined(PMU_VERSION)
    SetFllSoCFrequency((unsigned int)10000000);
    SetFllClusterFrequency((unsigned int)80000000);
    
    for (i=1; i<32; i++) { // SIZE
      for (j=0; j<8; j++) { // TCDM ADDR
        for (k=0; k<8; k++) { // EXT ADDR
          for (l=0; l<2; l++) { // TYPE
            error_count += testMCHAN(i,l,INC,LIN,EXT_DATA_ADDR+k,TCDM_DATA_ADDR+j,0,0);
          }
        }
      }
    }
    
    SetFllSoCFrequency((unsigned int)80000000);
    SetFllClusterFrequency((unsigned int)10000000);
    
    for (i=1; i<32; i++) { // SIZE
      for (j=0; j<8; j++) { // TCDM ADDR
        for (k=0; k<8; k++) { // EXT ADDR
          for (l=0; l<2; l++) { // TYPE
            error_count += testMCHAN(i,l,INC,LIN,EXT_DATA_ADDR+k,TCDM_DATA_ADDR+j,0,0);
          }
        }
      }
    }
#endif
    
  }
  
  printf("error count: %d\n", error_count);
  
  return error_count;
  
}

int testMCHAN(unsigned int len, char type, char incr, char twd, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride ){
  
  unsigned int i;
  unsigned int cmd;
  volatile char test,read;
  static int error = 0;
  int id;
  
  if (type == 0){
#ifdef VERBOSE
    printf ("STARTING TEST FOR ST %d OPERATION. TCDM ADDR= %8x, EXT ADDR = %8x \n",len,tcdm_addr,ext_addr);
#endif
    for (i=0; i<len; i++){
      *(char*)(tcdm_addr + i) = (char)(i + len + type + ( tcdm_addr & 0xFF ) + ( ext_addr & 0xFF ) );
    }
  }else{
#ifdef VERBOSE
    printf ("STARTING TEST FOR LD %d OPERATION. TCDM ADDR= %8x, EXT ADDR = %8x \n",len,tcdm_addr,ext_addr);
#endif
    for (i=0; i<len; i++){
      *(char*)(ext_addr + i) = (char)(i + len + type + ( tcdm_addr & 0xFF ) + ( ext_addr & 0xFF ) );
    }
  }
  
  id = mchan_alloc();
  
  mchan_transfer(len, type, incr, twd, 1, 0, 0, ext_addr, tcdm_addr, 0, 0);
  
  mchan_barrier(id);
  
  mchan_free(id);
  
  if (type == 0)
    for (i=0; i<len; i++){
      test = (char)(i + len + type + ( tcdm_addr & 0xFF ) + ( ext_addr & 0xFF ) );
      read = *(char*)(ext_addr + i);
      if ( test != read ){
        printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
        error++;
      }
    }
  else
    {
      for (i=0; i<len; i++){
        test = (char)(i + len + type + ( tcdm_addr & 0xFF ) + ( ext_addr & 0xFF ) );
        read = *(char*)(tcdm_addr + i);
        if ( test != read ){
          printf("Error!!! Read: %x, Test:%x, Index: %d \n ",read,test,i);
          error++;
        }
      }
    }
  
  return error;
  
}
