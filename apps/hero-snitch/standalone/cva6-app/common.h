
#pragma once

#include <stddef.h>
#include <stdint.h>

#define SHELL_RED "\033[0;31m"
#define SHELL_GRN "\033[0;32m"
#define SHELL_RST "\033[0m"

/**
 * @brief Test memory access by writing and reading all elements
 * @details
 */
int memtest(void* mem, size_t size, const char* cmt, uint8_t fillPat);

/**
 * @brief Print memory to stdout
 *
 * @param data pointer to the data
 * @param size number of bytes
 */
void hexdump(const void *data, size_t size);
