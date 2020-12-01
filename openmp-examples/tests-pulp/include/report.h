#ifndef __REPORT_H__
#define __REPORT_H__

#include <assert.h>
#include <stdio.h>
#include <stdlib.h> // abort()

void __assert_func(const char* file, int line, const char* funcname, const char* assertion) {
  printf("Assertion `%s' in %s (%s:%d) failed!\n", assertion, funcname, file, line);
  abort();
}

unsigned report_pass_fail(unsigned (*fn)(), const char* name)
{
  printf("Testing %s ..\n", name);
  if (fn()) {
    return 0;
  } else {
    printf("%s failed!\n", name);
    return 1;
  }
}

unsigned report_n_errors(unsigned (*fn)(), const char* name)
{
  printf("Testing %s ..\n", name);
  const unsigned n_errors = fn();
  if (n_errors == 0) {
    return 0;
  } else {
    printf("%s failed with %d errors!\n", name, n_errors);
    return n_errors;
  }
}

#endif
