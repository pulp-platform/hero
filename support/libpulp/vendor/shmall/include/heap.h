#ifndef HEAP_H
#define HEAP_H

#include <stdint.h>
#include <stddef.h>
#include "pulp_common.h"

#define HEAP_INIT_SIZE L3_MEM_SIZE_B
#define HEAP_MAX_SIZE L3_MEM_SIZE_B
#define HEAP_MIN_SIZE L3_MEM_SIZE_B

#define MIN_ALLOC_SZ 4

#define MIN_WILDERNESS 0x2000
#define MAX_WILDERNESS 0x1000000

#define BIN_COUNT 8
#define BIN_MAX_IDX (BIN_COUNT - 1)

typedef unsigned int uint;

typedef struct node_t {
    uint hole;
    uint size;
    struct node_t* next;
    struct node_t* prev;
    uint8_t pad[8 - ((2*sizeof(uint)+2*sizeof(struct node_t*)) % 8)]; // pad size to 8B alignment
} node_t;

typedef struct { 
    node_t *header;
    uint8_t pad[8 - (sizeof(node_t*) % 8)]; // pad size to 8B alignment
} footer_t;

typedef struct {
    node_t* head;
} bin_t;

typedef struct {
    long start;
    long end;
    bin_t *bins[BIN_COUNT];
} heap_t;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
static uint overhead = sizeof(footer_t) + sizeof(node_t);
#pragma GCC diagnostic pop

void init_heap(heap_t *heap, long start);

void *heap_alloc(heap_t *heap, size_t size);
void heap_free(heap_t *heap, void *p);
uint expand(heap_t *heap, size_t sz);
void contract(heap_t *heap, size_t sz);

uint get_bin_index(size_t sz);
void create_foot(node_t *head);
footer_t *get_foot(node_t *head);

node_t *get_wilderness(heap_t *heap);

#endif
