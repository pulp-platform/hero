#ifndef MY_SLEEP_H
#define MY_SLEEP_H

/* adapted from llvm test suite 
   https://github.com/llvm-mirror/openmp/blob/master/runtime/test/omp_my_sleep.h
*/

static void my_sleep(double sleeptime){
	int i;
	for (i=0;i<sleeptime;i++){}
}

#endif // MY_SLEEP_H
