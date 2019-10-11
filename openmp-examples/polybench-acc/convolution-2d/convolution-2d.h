/**
 * adi.h: This file is part of the PolyBench/C 3.2 test suite.
 *
 *
 * Contact: Louis-Noel Pouchet <pouchet@cse.ohio-state.edu>
 * Web address: http://polybench.sourceforge.net
 */
#ifndef CONV2D_H
#define CONV2D_H

/* Default to LARGE_DATASET. */
# if !defined(MINI_DATASET) && !defined(SMALL_DATASET) && !defined(LARGE_DATASET) && !defined(EXTRALARGE_DATASET)
#  define EXTRAMINI_DATASET
# endif

/* Do not define anything if the user manually defines the size. */
# if !defined(NI) && ! defined(NJ)
/* Define the possible dataset sizes. */
#  ifdef EXTRAMINI_DATASET
#   define NI 8
#   define NJ 8
#  endif

#  ifdef MINI_DATASET
#   define NI 64
#   define NJ 64
#  endif

#  ifdef SMALL_DATASET
#   define NI 1024
#   define NJ 1024
#  endif

#  ifdef STANDARD_DATASET
#   define NI 2048
#   define NJ 2048
#  endif

#  ifdef LARGE_DATASET /* Default if unspecified. */
#   define NI 4096
#   define NJ 4096
#  endif

#  ifdef EXTRALARGE_DATASET
#   define NI 8192
#   define NJ 8192
#  endif
# endif /* !N */

# define _PB_NI POLYBENCH_LOOP_BOUND(NI,ni)
# define _PB_NJ POLYBENCH_LOOP_BOUND(NJ,nj)

# ifndef DATA_TYPE
#  define DATA_TYPE int
#  define DATA_PRINTF_MODIFIER "%d "
# endif


#endif /* !CONV2D */
