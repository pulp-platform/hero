// SPM_SIZE in ints
#define SPM_SIZE (128*1024/4)

#if defined(__PULP__) || defined(PULP)
#ifdef __llvm__
#define DMA_DATA_TYPE __device int*
#else
#define DMA_DATA_TYPE int*
#endif
#else
#define DMA_DATA_TYPE int*
#endif

DMA_DATA_TYPE alloc_spm(void);

void memcpy_to_spm(DMA_DATA_TYPE spm, void* ram, size_t len);

void memcpy_from_spm(void* ram, DMA_DATA_TYPE spm, size_t len);

void dma_flush(void);
