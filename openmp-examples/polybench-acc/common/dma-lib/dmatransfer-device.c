#include "pulp.h"
#include "dmatransfer.h"

#define PULP_DMA_MAX_XFER_SIZE_B 32768
#define DMA_MAX_JOBS 16
#define DEBUG(...)

int pending_dma_jobs = 0;
char partial_flush_low = 0;

inline void try_flush_intermed(void) {
    if (pending_dma_jobs >= DMA_MAX_JOBS) {
        DEBUG("max jobs reached, flushing\n");
        int low = partial_flush_low ? 0 : DMA_MAX_JOBS / 2;
        int high = partial_flush_low ? DMA_MAX_JOBS / 2 : DMA_MAX_JOBS;
        partial_flush_low = !partial_flush_low;

        for(int job = low; job < high; job++) {
            plp_dma_wait(job);
            pending_dma_jobs--;
        }
    }
}

inline void __prem_dma_flush(void) {
    DEBUG("__prem_dma_flush()\n");
    for(int job = 0; job < DMA_MAX_JOBS; job++) {
        plp_dma_wait(job);
    }
    pending_dma_jobs = 0;
}

// Adapted code form libhero-target
inline int pulp_dma_memcpy_1d(void* loc_addr, void* ext_addr, size_t len, int ext2loc) {
    uint32_t dma_job = plp_dma_counter_alloc();
    uint32_t dma_cmd;

    while (len > 0) {
        int len_tmp;
        if (len > PULP_DMA_MAX_XFER_SIZE_B)
            len_tmp = PULP_DMA_MAX_XFER_SIZE_B;
        else
            len_tmp = len;

        //printf("copy cmd: loc: 0x%x ext: 0x%x ext2loc: %d len: %d\n", loc_addr, ext_addr, ext2loc, len);
        dma_cmd = plp_dma_getCmd(ext2loc, len_tmp, PLP_DMA_1D, PLP_DMA_TRIG_EVT,
            PLP_DMA_NO_TRIG_IRQ, PLP_DMA_PRIV);
        __asm__ __volatile__ ("" : : : "memory");
        plp_dma_cmd_push(dma_cmd, loc_addr, ext_addr);

        len     -= len_tmp;
        ext_addr += len_tmp;
        loc_addr += len_tmp;
    }

    return dma_job;
}

inline void __prem_dma_memcpy_to_spm_1d(void* spm, void* ram, size_t len) {
    DEBUG("__prem_dma_memcpy_to_spm_1d(0x%x, 0x%x, 0x%x)\n", spm, ram, len);
    try_flush_intermed();
    pulp_dma_memcpy_1d(spm, ram, len, 1);
    pending_dma_jobs++;
    DEBUG("__prem_dma_memcpy_to_spm_1d post\n");
}

inline void __prem_dma_memcpy_from_spm_1d(void* ram, void* spm, size_t len) {
    DEBUG("__prem_dma_memcpy_from_spm_1d(0x%x, 0x%x, 0x%x)\n", ram, spm, len);
    try_flush_intermed();
    pulp_dma_memcpy_1d(spm, ram, len, 0);
    pending_dma_jobs++;
    DEBUG("__prem_dma_memcpy_from_spm_1d post\n");
}


/////////////////////////////////////////////////
/////////////////////////////////////////////////
/////////////////////////////////////////////////

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

void memcpy_to_spm(DMA_DATA_TYPE spm, void* ram, size_t len) {
    __prem_dma_memcpy_to_spm_1d(spm, ram, len*4);
}


void memcpy_from_spm(void* ram, DMA_DATA_TYPE spm, size_t len) {
    __prem_dma_memcpy_from_spm_1d(ram, spm, len*4);
}

void dma_flush(void) {
    __prem_dma_flush();
}
