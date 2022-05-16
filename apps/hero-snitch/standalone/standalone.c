/*
 * bigPULP standalone application launcher
 *
 * Copyright 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 * Author: Noah Huetter <huettern@iis.ee.ethz.ch>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <errno.h>
#include <stdlib.h>
#include <string.h>

#include "libsnitch.h"

void print_usage() {
  printf("Noah Huetter - huettern@iis.ee.ethz.ch\n\n");
  printf("Usage: ./standalone [app] [timeout] [cluster] [log]\n");
  printf("  app      If specified, run this application on the Snitch cluster.\n");
  printf("           If empty, print cluster info and exit.\n");
  printf("  timeout  Timeout in seconds to wait for end of computation (default = 5)\n");
  printf("  cluster  Cluster index (default = 0)\n");
  printf("  log      Library log level (default = 0)\n");
}

int main(int argc, char *argv[]) {
  int ret;
  snitch_dev_t *snitch;
  snitch_dev_t **clusters;

  printf("Snitch Standalone Application Launcher\n");

  /*
   * Preparation
   */
  char app_name[50];
  unsigned int timeout_s = 5;
  unsigned int cluster_idx = 0;
  unsigned int log_level = 0;

  if ((argc == 2) && !strcmp("-h", argv[1])) {
    print_usage();
    return -EINVAL;
  } else if (argc > 5) {
    printf(
        "WARNING: More than 4 command line arguments are not supported. Those will be ignored. "
        "Type -h for help.\n");
  }

  if (argc > 1) strcpy(app_name, argv[1]);
  if (argc > 2) timeout_s = atoi(argv[2]);
  if (argc > 3) cluster_idx = atoi(argv[3]);
  if (argc > 4) log_level = atoi(argv[4]);

  // No app specified discover and exit
  snitch_set_log_level(LOG_INFO);
  if (argc < 2) {
    snitch_discover(NULL, NULL, NULL);
    return 0;
  }
  
  return 0;
}
