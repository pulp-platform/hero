#include <stdio.h>
#include <stdint.h>
#include "hal/pulp.h"
#include "pulp.h"

#define UINT8_NUMBER(i)       ((i) & 0xFF),
#define UINT8_NUMBER_XOR(i)   (((i) & 0xFF) ^ 0x23),
#define UINT8_ZERO(i)         0x0,

#define REPEATINC1(    X, i)       X(i)
#define REPEATINC2(    X, i)       REPEATINC1    (X, i)       REPEATINC1    (X, i +     1)
#define REPEATINC3(    X, i)       REPEATINC2    (X, i)       REPEATINC1    (X, i +     2)
#define REPEATINC4(    X, i)       REPEATINC2    (X, i)       REPEATINC2    (X, i +     2)
#define REPEATINC5(    X, i)       REPEATINC4    (X, i)       REPEATINC1    (X, i +     4)
#define REPEATINC7(    X, i)       REPEATINC4    (X, i)       REPEATINC3    (X, i +     4)
#define REPEATINC8(    X, i)       REPEATINC4    (X, i)       REPEATINC4    (X, i +     4)
#define REPEATINC9(    X, i)       REPEATINC8    (X, i)       REPEATINC1    (X, i +     8)
#define REPEATINC11(   X, i)       REPEATINC8    (X, i)       REPEATINC3    (X, i +     8)
#define REPEATINC13(   X, i)       REPEATINC8    (X, i)       REPEATINC5    (X, i +     8)
#define REPEATINC15(   X, i)       REPEATINC8    (X, i)       REPEATINC7    (X, i +     8)
#define REPEATINC16(   X, i)       REPEATINC8    (X, i)       REPEATINC8    (X, i +     8)
#define REPEATINC17(   X, i)       REPEATINC16   (X, i)       REPEATINC1    (X, i +    16)
#define REPEATINC19(   X, i)       REPEATINC16   (X, i)       REPEATINC3    (X, i +    16)
#define REPEATINC21(   X, i)       REPEATINC16   (X, i)       REPEATINC5    (X, i +    16)
#define REPEATINC23(   X, i)       REPEATINC16   (X, i)       REPEATINC7    (X, i +    16)
#define REPEATINC27(   X, i)       REPEATINC16   (X, i)       REPEATINC11   (X, i +    16)
#define REPEATINC29(   X, i)       REPEATINC16   (X, i)       REPEATINC13   (X, i +    16)
#define REPEATINC31(   X, i)       REPEATINC16   (X, i)       REPEATINC15   (X, i +    16)
#define REPEATINC32(   X, i)       REPEATINC16   (X, i)       REPEATINC16   (X, i +    16)
#define REPEATINC37(   X, i)       REPEATINC32   (X, i)       REPEATINC5    (X, i +    32)
#define REPEATINC41(   X, i)       REPEATINC32   (X, i)       REPEATINC9    (X, i +    32)
#define REPEATINC43(   X, i)       REPEATINC32   (X, i)       REPEATINC11   (X, i +    32)
#define REPEATINC47(   X, i)       REPEATINC32   (X, i)       REPEATINC15   (X, i +    32)
#define REPEATINC53(   X, i)       REPEATINC32   (X, i)       REPEATINC21   (X, i +    32)
#define REPEATINC59(   X, i)       REPEATINC32   (X, i)       REPEATINC27   (X, i +    32)
#define REPEATINC64(   X, i)       REPEATINC32   (X, i)       REPEATINC32   (X, i +    32)
#define REPEATINC128(  X, i)       REPEATINC64   (X, i)       REPEATINC64   (X, i +    64)
#define REPEATINC256(  X, i)       REPEATINC128  (X, i)       REPEATINC128  (X, i +   128)
#define REPEATINC512(  X, i)       REPEATINC256  (X, i)       REPEATINC256  (X, i +   256)
#define REPEATINC1024( X, i)       REPEATINC512  (X, i)       REPEATINC512  (X, i +   512)
#define REPEATINC2048( X, i)       REPEATINC1024 (X, i)       REPEATINC1024 (X, i +  1024)
#define REPEATINC4096( X, i)       REPEATINC2048 (X, i)       REPEATINC2048 (X, i +  2048)
#define REPEATINC8192( X, i)       REPEATINC4096 (X, i)       REPEATINC4096 (X, i +  4096)
#define REPEATINC10240(X, i)       REPEATINC8192 (X, i)       REPEATINC2048 (X, i +  8192)
#define REPEATINC16384(X, i)       REPEATINC8192 (X, i)       REPEATINC8192 (X, i +  8192)
#define REPEATINC32768(X, i)       REPEATINC16384(X, i)       REPEATINC16384(X, i + 16384)
#define REPEATINC40960(X, i)       REPEATINC32768(X, i)       REPEATINC8192 (X, i + 16384)
#define REPEATINC65536(X, i)       REPEATINC32768(X, i)       REPEATINC32768(X, i + 32768)

#define REPEATINC(C,X)      REPEATINC##C(X, 0)

uint8_t exp_uint8_number(unsigned int i);
uint8_t exp_uint8_number_xor(unsigned int i);

unsigned int lfsr_step(unsigned int reg);
int rand();

void dma_random(testresult_t* result,
                uint8_t* l2,
                unsigned int l2_len,
                uint8_t* tcdm,
                unsigned int tcdm_len,
                uint8_t (*exp_func)(unsigned int));

void dma_l2_to_tcdm(testresult_t *result,
                uint8_t* l2,
                unsigned int l2_offset, // in bytes
                unsigned int l2_len,    // in bytes
                uint8_t* tcdm,
                unsigned int tcdm_offset, // in bytes
                unsigned int tcdm_len,  // in bytes
                unsigned int dma_len,   // in bytes
                uint8_t (*exp_func)(unsigned int));
