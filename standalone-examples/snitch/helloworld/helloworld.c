#include "debug.h"
#include "snrt.h"

int main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;
  unsigned core_idx = snrt_cluster_core_idx();
  unsigned core_num = snrt_cluster_core_num();

  if (core_idx == 0) {
    snrt_trace("Hello World from core %d/%d!\n", core_idx, core_num);
  }

  return 0;
}
