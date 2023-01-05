
#include "common.h"
#include <stdio.h>

/**
 * @brief Test memory access by writing and reading all elements
 * @details
 */
int memtest(void *mem, size_t size, const char *cmt, uint8_t fillPat) {
  unsigned char rb;
  int err_cnt = 0;
  int test_cnt = 0;
  unsigned char *pmem = (unsigned char *)mem;

  printf("[memtest] %s size %ldKiB\n", cmt, size / 1024);

  size_t byte_off;
  for (byte_off = 0; byte_off < size; byte_off++) {
    if ((byte_off > 0) && ((byte_off % (64 * 1024)) == 0)) {
      printf(".");
      fflush(stdout);
    }

    pmem[byte_off] = byte_off % 0xff;
    rb = pmem[byte_off];
    if (rb != (byte_off % 0xff)) {
      printf("[memtest] error at off 0x%08lx, write 0x%02lx, read %02x\n", byte_off,
             byte_off % 0xff, rb);
      err_cnt++;
    }
    test_cnt++;

    pmem[byte_off] = fillPat;
    rb = pmem[byte_off];
    if (rb != fillPat) {
      printf("[memtest] error at off 0x%08lx, write 0x%02x, read %02x\n", byte_off, fillPat, rb);
      err_cnt++;
    }
    test_cnt++;
    if (err_cnt > 8) {
      printf("aborting due to too many errors\n");
      break;
    }
  }
  printf("\r[memtest] %s %s - size: %ld (%ldk), writes performed: %d, errors: %d (%.2f%%)\n",
         err_cnt ? SHELL_RED "FAIL" SHELL_RST : SHELL_GRN "PASS" SHELL_RST, cmt, size, size / 1024,
         test_cnt, err_cnt, 100.0 / test_cnt * err_cnt);
  return err_cnt;
}

/**
 * @brief Simple hex dump routine from https://gist.github.com/ccbrown/9722406
 *
 * @param data
 * @param size
 */
void hexdump(const void *data, size_t size) {
  char ascii[17];
  size_t i, j;
  uint32_t pad = 4;
  ascii[16] = '\0';
  for (i = 0; i < size; ++i) {
    if (i % 16 == 0)
      printf("%0*lx: ", pad, i);
    printf("%02X ", ((unsigned char *)data)[i]);
    if (((unsigned char *)data)[i] >= ' ' && ((unsigned char *)data)[i] <= '~') {
      ascii[i % 16] = ((unsigned char *)data)[i];
    } else {
      ascii[i % 16] = '.';
    }
    if ((i + 1) % 8 == 0 || i + 1 == size) {
      printf(" ");
      if ((i + 1) % 16 == 0) {
        printf("|  %s \n", ascii);
      } else if (i + 1 == size) {
        ascii[(i + 1) % 16] = '\0';
        if ((i + 1) % 16 <= 8) {
          printf(" ");
        }
        for (j = (i + 1) % 16; j < 16; ++j) {
          printf("   ");
        }
        printf("|  %s \n", ascii);
      }
    }
  }
}
