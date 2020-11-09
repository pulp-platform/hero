// SPM_SIZE in ints
#define SPM_SIZE (92 * 1024 / 4)

#include <stdint.h>
#include <stddef.h>

#if defined(__llvm__)
#define DEVICE_PTR __device int*
#define HOST_PTR __host int*
#else
#define HOST_PTR uint64_t
#define DEVICE_PTR uint32_t
#endif

#pragma omp declare target

DEVICE_PTR alloc_spm(void);
void dealloc_spm(DEVICE_PTR);

void memcpy_to_spm(DEVICE_PTR spm, HOST_PTR ram, uint32_t len);
void memcpy_from_spm(HOST_PTR ram, DEVICE_PTR spm, uint32_t len);

void dma_flush(void);

static void __attribute__((used)) try_flush_intermed(void);
static void __attribute__((used)) __prem_dma_flush(void);
static int __attribute__((used)) pulp_dma_memcpy_1d(void* loc_addr, void* ext_addr, size_t len, int ext2loc);
static void __attribute__((used)) __prem_dma_memcpy_to_spm_1d(void* spm, void* ram, size_t len);
static void __attribute__((used)) __prem_dma_memcpy_from_spm_1d(void* ram, void* spm, size_t len);

#pragma omp end declare target
