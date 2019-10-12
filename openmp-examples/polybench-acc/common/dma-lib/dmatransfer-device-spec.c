#include "pulp.h"
#include "dmatransfer.h"

void* global_buffer = NULL;
DMA_DATA_TYPE alloc_spm(void) {
    void* buffer;
    if (global_buffer == NULL) {
        rt_alloc_t* allocator = rt_alloc_l1(0);
        buffer = rt_user_alloc_align(allocator, SPM_SIZE * sizeof(int), 4);
        global_buffer = buffer;
    } else {
        buffer = global_buffer;
    }
    return buffer;
}
void dealloc_spm(DMA_DATA_TYPE ptr) {
    if(global_buffer == NULL) {
        rt_alloc_t* allocator = rt_alloc_l1(0);
        rt_user_free(allocator, ptr, SPM_SIZE * sizeof(int));
    }
}

void memcpy_to_spm(DMA_DATA_TYPE spm, void* ram, size_t len) {
    int * dst = (int *) spm;
    int * src = (int *) ram;

    reset_timer();
    start_timer();
    #pragma omp parallel for schedule(static, 1) num_threads(1)
    for(int i = 0; i < len; i++) {
        dst[i] = src[i];
    }
    stop_timer();
    int cyc = get_time();
    printf("TTT: %d\n", cyc);
}


void memcpy_from_spm(void* ram, DMA_DATA_TYPE spm, size_t len) {
    memcpy_to_spm(ram, spm, len);
}

void dma_flush(void) {
}
