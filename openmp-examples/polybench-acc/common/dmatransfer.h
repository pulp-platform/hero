// SPM_SIZE in ints
#define SPM_SIZE (128*1024/4)

int* alloc_spm(void);

void memcpy_to_spm(void* spm, void* ram, size_t len);


void memcpy_from_spm(void* ram, void* spm, size_t len);

void dma_flush(void);
