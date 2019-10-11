#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dmatransfer.h"

int* alloc_spm() {
    return malloc(SPM_SIZE * sizeof(int));
}

void memcpy_to_spm(void* spm, void* ram, size_t len) {
    //printf("Warning: Using normal memcpy!\n");
    memcpy(spm, ram, len*4);
}


void memcpy_from_spm(void* ram, void* spm, size_t len) {
    //printf("Warning: Using normal memcpy!\n");
    memcpy(ram, spm, len*4);
}

void dma_flush() {
}
