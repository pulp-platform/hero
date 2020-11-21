/* Adapted from OpenMP Testsuite */

#ifndef OMP_TESTSUITE_H
#define OMP_TESTSUITE_H

#include <stdio.h>
#include <stdlib.h>

/* General                                                */
/**********************************************************/
#define LOOPCOUNT 100 /* Number of iterations to slit amongst threads */
#define REPETITIONS 1 /* Number of times to run each test */

#define SLEEPTIME 1000

/* Definitions for tasks                                  */
/**********************************************************/
#define NUM_TASKS 25
#define MAX_TASKS_PER_THREAD 5

#define fprintf(dev, fmt,  ...) \
  printf(fmt, ##__VA_ARGS__);

#endif
