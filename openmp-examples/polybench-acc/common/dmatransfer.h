// SPM_SIZE in ints
#define SPM_SIZE (92*1024/4)

#include <stdint.h>

#if defined(__llvm__)
#  define DEVICE_PTR __device int*
#  define HOST_PTR __host int*
#else
#  define HOST_PTR uint64_t
#  define DEVICE_PTR uint32_t
#endif

#pragma omp declare target

DEVICE_PTR alloc_spm(void);
void dealloc_spm(DEVICE_PTR);

void memcpy_to_spm(DEVICE_PTR spm, HOST_PTR ram, uint32_t len);
void memcpy_from_spm(HOST_PTR ram, DEVICE_PTR spm, uint32_t len);

void dma_flush(void);

#pragma omp end declare target
