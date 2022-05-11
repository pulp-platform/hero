/*
 * @Author: Noah Huetter
 * @Date:   2020-09-25 14:29:49
 * @Last Modified by:   Noah Huetter
 * @Last Modified time: 2020-10-23 15:01:24
 */

/**
 * This is a very simple implementation of the RISC-V front end server
 * Intended to use for only a single snitch cluster
 *
 */

#include "fesrv.h"
#include "debug.h"

#include <assert.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

// #define dbg(...) printf(__VA_ARGS__)
#define dbg(fmt, ...)

#define SYS_exit 60
#define SYS_write 64
#define SYS_read 63
#define SYS_wake 1235
#define SYS_cycle 1236

static void handleSyscall(fesrv_t *fs, uint64_t magicMem[6]);

#define PUTCHAR_BUF_SIZE 200

#define DBG_LOG
#define XSTR(var) #var

/**
 * @brief Init front end server with default settings
 * @param fs pointer to front end server struct
 * @param a2h_rb_p physical address of a2h ring buffer is stored here to be passed to the
 * accelerator
 */
void fesrv_init(fesrv_t *fs, snitch_dev_t *dev, void **a2h_rb_p) {
  void *addr;

  fs->dev = dev;
  fs->pollInterval = 10 * 1000; // [us]
  fs->abortAfter = 0;

  // state
  fs->abort = false;
  fs->nCalls = 0;
  fs->coreExited = 0;

  // allocate an acceleartor to host ring buffer where each element is 6*sizeof(uint64_t) to support
  // syscalls to fesrv
  const unsigned a2hrb_element_size = sizeof(uint64_t) * 6;
  const unsigned a2hrb_elements = 16;
  fs->a2h_rb = (struct ring_buf *)snitch_l3_malloc(fs->dev, sizeof(struct ring_buf), a2h_rb_p);
  assert(fs->a2h_rb);
  fs->a2h_rb->data_v =
      (uint64_t)snitch_l3_malloc(fs->dev, a2hrb_element_size * a2hrb_elements, &addr);
  assert(fs->a2h_rb->data_v);
  fs->a2h_rb->data_p = (uint64_t)addr;
  rb_init(fs->a2h_rb, a2hrb_elements, a2hrb_element_size);

  // putchar buffer
  fs->putCharBuf = malloc(PUTCHAR_BUF_SIZE * sizeof(char));
  assert(fs->putCharBuf);
  fs->putCharIdx = 0;

  // file logging
  fs->stdout_file = fopen("fesrv_stdout.log", "a");
#ifdef DBG_LOG
  fs->logfile = fopen("fesrv.log", "w");
#endif
}

static volatile int g_interrupt = 0;

static void intHandler(int dummy) {
  g_interrupt = 1;
  pr_info("[fesrv] Caught signal, aborting\n");
}

/**
 * @brief Runs the front end server. Best to run this as a thread
 * @details
 *
 * @param fs pointer to the front end server struct
 */
void fesrv_run(fesrv_t *fs) {
  uint64_t magicMem[6];
  bool autoAbort;
  useconds_t tstart;
  int ret;
  uint32_t prev_tail = 0;
  const char *abort_reason;

  g_interrupt = 0;
  signal(SIGINT, intHandler);

  pr_info("[fesrv] Start polling\n");

  // check if we need to autoabort
  autoAbort = (fs->abortAfter > 0) ? true : false;

  /**
   * Polling loop for tohost variable
   */
  bool abort = false;
  bool wait = true;
  tstart = time(NULL);

  while (!abort) {

    // try to pop a value
    // snitch_flush(fs->dev);
    ret = rb_host_get(fs->a2h_rb, magicMem);

    if (ret == 0) {
      // reset abort timer
      tstart = time(NULL);

      // check for tail-skip
      if (((prev_tail + 1) % fs->a2h_rb->size) != fs->a2h_rb->tail) {
        pr_error("ERROR: tail skipped from %d to %d!!!\n", prev_tail, fs->a2h_rb->tail);
        pr_error("This usually means the buffer area was overwritten. Perhaps you didn't allocate "
               "enough\n");
        pr_error("memory in the last call to snitch_l3_malloc before fesrv_init?\n");
      }
      prev_tail = fs->a2h_rb->tail;
      dbg("[fesrv]   0: %#lx 1: %#lx", magicMem[0], magicMem[1]);
      dbg(" 2: %#lx (%c) 3: %#lx", magicMem[2], (char)magicMem[2], magicMem[3]);
      dbg(" 4: %#lx 5: %#lx\n", magicMem[4], magicMem[5]);
      // dont wait this round
      wait = false;

      // process
      fs->nCalls++;
      handleSyscall(fs, magicMem);

#ifdef DBG_LOG
      struct timespec tv;
      clock_gettime(CLOCK_REALTIME, &tv);
      fprintf(fs->logfile, "%lu,%ld,%lu,%lu,%lu,%lu,%lu\n",
              (tv.tv_sec) * 1000 + (tv.tv_nsec) / 1000000, magicMem[0], magicMem[1], magicMem[2],
              magicMem[3], magicMem[4], magicMem[5]);
#endif
    }
    // only wait if nothing received
    if (wait)
      usleep(fs->pollInterval);
    wait = true;

    // check for abort
    if (fs->abort) {
      abort = true;
      abort_reason = "external";
    }
    if (autoAbort && (time(NULL) > (tstart + fs->abortAfter))) {
      abort = true;
      abort_reason = "timeout";
    }
    if (fs->coreExited) {
      abort = true;
      abort_reason = "exit code";
    }
    if (g_interrupt) {
      abort = true;
      abort_reason = "interrupt";
    }
  }

  fclose(fs->stdout_file);
#ifdef DBG_LOG
  fclose(fs->logfile);
#endif
  signal(SIGINT, SIG_DFL);
  pr_info("[fesrv] Exiting (%s). Syscalls processed: %ld Exit code received? %s: %d\n", abort_reason,
         fs->nCalls, fs->coreExited ? "Yes" : "No", fs->exitCode);
}

/**
 * @brief processes the system call
 * @details
 *
 * @param magicMem magic memory passed from snitch to host
 */
static void handleSyscall(fesrv_t *fs, uint64_t magicMem[6]) {
  bool handled = false;

  switch (magicMem[0]) {
  case SYS_write:
    // _putchar
    if ((magicMem[1] == 1) && (magicMem[3] == 1)) {
      handled = true;
      dbg("[fesrv]   putchar - %c\n", (char)magicMem[2]);
      fs->putCharBuf[fs->putCharIdx++] = magicMem[2];
      if (magicMem[2] == '\n' || (fs->putCharIdx == PUTCHAR_BUF_SIZE - 1)) {
        if (fs->putCharIdx == PUTCHAR_BUF_SIZE - 1)
          pr_warn("[fesrv] Warning: putchar buffer limit reached!\n");
        // null-terminate and remove \r and/or \n
        fs->putCharBuf[fs->putCharIdx] = '\0';
        fs->putCharBuf[strcspn(fs->putCharBuf, "\r\n")] = 0;
        fprintf(fs->stdout_file, "%s\n", fs->putCharBuf);
        printf("%s\n", fs->putCharBuf);
        fflush(stdout);

        // reset pointer
        fs->putCharIdx = 0;
      }
    }
    break;
  case SYS_read:

    break;
  case SYS_exit:
    handled = true;
    pr_info("[fesrv]   Exited with code %d (%#lx)\n", (int)magicMem[1], magicMem[1]);
    fs->coreExited = 1;
    fs->exitCode = (int)magicMem[1];
    break;
  case SYS_wake:
    handled = true;
    pr_info("[fesrv]   wake %#x\n", (uint32_t)magicMem[1]);
    break;
  case SYS_cycle:
    // handled = true;
    // fs->cyclesReported[core] = magicMem[1];
    // printf("[fesrv]   reports %lu cycles\n", fs->cyclesReported[core]);
  default:
    break;
  }

  if (!handled) {
    pr_error("[fesrv] Unknown syscall\n");
    pr_error("[fesrv]   0: %016lx 1: %016lx\n", magicMem[0], magicMem[1]);
    pr_error("[fesrv]   2: %016lx 3: %016lx\n", magicMem[2], magicMem[3]);
    pr_error("[fesrv]   4: %016lx 5: %016lx\n", magicMem[4], magicMem[5]);
  }
}
