#include "random_helper.h"
#include "mchan_tests.h"

//#define VERBOSE 1

extern uint32_t g_lfsr;

void dma_random(testresult_t* result,
                uint8_t* l2,
                unsigned int l2_len,
                uint8_t* tcdm,
                unsigned int tcdm_len,
                uint8_t (*exp_func)(unsigned int)) {
  unsigned int l2_offset = rand() % l2_len;
  unsigned int tcdm_offset = rand() % tcdm_len;
  unsigned int dma_len = (rand() % l2_len) % tcdm_len;

  if (l2_offset + dma_len > l2_len)
    dma_len = l2_len - l2_offset;

  if (tcdm_offset + dma_len > tcdm_len)
    dma_len = tcdm_len - tcdm_offset;

  dma_l2_to_tcdm(result, l2, l2_offset, l2_len, tcdm, tcdm_offset, tcdm_len, dma_len, exp_uint8_number);
}

void dma_l2_to_tcdm(testresult_t *result,
                uint8_t* l2,
                unsigned int l2_offset, // in bytes
                unsigned int l2_len, // in bytes
                uint8_t* tcdm,
                unsigned int tcdm_offset, // in bytes
                unsigned int tcdm_len, // in bytes
                unsigned int dma_len, // in bytes
                uint8_t (*exp_func)(unsigned int)) {
  unsigned int i;
  unsigned int id;

  if(get_core_id() == 0) {
    // check if our parameters are sane
    if ((l2_offset + dma_len) > l2_len || (tcdm_offset + dma_len) > tcdm_len) {
      printf("Request is not sane!\n");
      result->errors++;
      return;
    }

#ifdef VERBOSE
    printf("Parameters were\nL2 offset %d\nTCDM offset %d\nDMA len %d\n", l2_offset, tcdm_offset, dma_len);
#endif

    // poison TCDM
    for(i = 0; i < tcdm_len; i++) {
      tcdm[i] = 0;
    }

    id = mchan_alloc();

    mchan_transfer(dma_len, RX, INC, LIN, 1, 0, 0, (int)&l2[l2_offset], (int)(&tcdm[tcdm_offset]), 0,0);
    mchan_barrier(id);
    mchan_free(id);


    // check if neighbors are still 0
    for(i = 0; i < tcdm_offset; i++) {
      if (tcdm[i] != 0) {
        result->errors++;
        printf("Check init: TCDM index %d should be 0, is %X\n", i, (unsigned int)tcdm[i]);
      }
    }

    for(i = 0; i < dma_len; i++) {
      if (tcdm[i + tcdm_offset] != exp_func(i + l2_offset)) {
        result->errors++;
        printf("Check DMA: TCDM index %d should be %X, is %X\n", i + tcdm_offset, (unsigned int)exp_func(i + l2_offset), (unsigned int)tcdm[i + tcdm_offset]);
      }
    }

    for(i = tcdm_offset+dma_len; i < tcdm_len; i++) {
      if (tcdm[i] != 0) {
        result->errors++;
        printf("Check fini: TCDM index %d should be 0, is %X\n", i, (unsigned int)tcdm[i]);
      }
    }
  }

  rt_team_barrier();
}


uint8_t exp_uint8_number(unsigned int i) {
  return i;
}

uint8_t exp_uint8_number_xor(unsigned int i) {
  return (i) ^ 0x23;
}

unsigned int lfsr_step(unsigned int reg) {
  // From https://www.schneier.com/paper-pseudorandom-sequence.html, example 1
  // This LFSR has a period of 2^32-1

  /*Register should be initialized with some random value.*/
  reg = ((((reg >> 31)  /*Shift the 32nd bit to the first
                                    bit*/
             ^ (reg >> 6)    /*XOR it with the seventh bit*/
             ^ (reg >> 4)    /*XOR it with the fifth bit*/
             ^ (reg >> 2)    /*XOR it with the third bit*/
             ^ (reg >> 1)    /*XOR it with the second bit*/
             ^ reg)          /*and XOR it with the first bit.*/
             & 0x0000001)         /*Strip all the other bits off and*/
             <<31)                /*move it back to the 32nd bit.*/
             | (reg >> 1);   /*Or with the register shifted
                                    right.*/
  return reg;
}

int rand() {
  g_lfsr = lfsr_step(g_lfsr);

  return g_lfsr;
}
