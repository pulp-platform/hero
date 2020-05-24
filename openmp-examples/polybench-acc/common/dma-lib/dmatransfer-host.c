#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "dmatransfer.h"

DEVICE_PTR alloc_spm(void) {
    void * addr = malloc(SPM_SIZE * sizeof(int));
    if (addr > UINT_MAX) {
      printf("SPM addr out of range!");
      return (DEVICE_PTR) NULL;
    }
    return (DEVICE_PTR) addr;
}
void dealloc_spm(DEVICE_PTR ptr) {
    free((void*)ptr);
}

void memcpy_to_spm(DEVICE_PTR spm, HOST_PTR ram, uint32_t len) {
    //printf("Warning: Using normal memcpy!\n");
    memcpy((void*)spm, (void*)ram, len*4);
}


void memcpy_from_spm(HOST_PTR ram, DEVICE_PTR spm, uint32_t len) {
    //printf("Warning: Using normal memcpy!\n");
    memcpy((void*)ram, (void*)spm, len*4);
}

void dma_flush(void) {
}
