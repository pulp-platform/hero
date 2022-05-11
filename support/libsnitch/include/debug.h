#pragma once

#include <stdint.h>
#include <stdio.h>

#include "libsnitch.h"

#define SHELL_RED "\033[0;31m"
#define SHELL_GRN "\033[0;32m"
#define SHELL_RST "\033[0m"

extern enum log_level g_debuglevel;

#define pr_error(fmt, ...)                                                                         \
  ({                                                                                               \
    if (LOG_ERROR <= g_debuglevel)                                                                 \
      printf("[ERROR libsnitch:%s()] " fmt, __func__, ##__VA_ARGS__);                              \
  })
#define pr_warn(fmt, ...)                                                                          \
  ({                                                                                               \
    if (LOG_WARN <= g_debuglevel)                                                                  \
      printf("[WARN  libsnitch:%s()] " fmt, __func__, ##__VA_ARGS__);                              \
  })
#define pr_info(fmt, ...)                                                                          \
  ({                                                                                               \
    if (LOG_INFO <= g_debuglevel)                                                                  \
      printf("[INFO  libsnitch:%s()] " fmt, __func__, ##__VA_ARGS__);                              \
  })
#define pr_debug(fmt, ...)                                                                         \
  ({                                                                                               \
    if (LOG_DEBUG <= g_debuglevel)                                                                 \
      printf("[DEBUG libsnitch:%s()] " fmt, __func__, ##__VA_ARGS__);                              \
  })
#define pr_trace(fmt, ...)                                                                         \
  ({                                                                                               \
    if (LOG_TRACE <= g_debuglevel)                                                                 \
      printf("[TRACE libsnitch:%s()] " fmt, __func__, ##__VA_ARGS__);                              \
  })

