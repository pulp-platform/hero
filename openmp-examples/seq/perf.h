#include <errno.h>
//extern int errno;
#ifdef TIMEKERN
#include <time.h>
#define CLOCK_PRECISION 1E9
typedef struct {
    time_t tv_sec;
      long tv_nsec;
} my_timespec;

  my_timespec KernStrt, KernStop;
    void eval_kern_time(my_timespec KernStrt, my_timespec KernStop){

          double accum = (KernStop.tv_sec - KernStrt.tv_sec) +
                        (KernStop.tv_nsec - KernStrt.tv_nsec) / CLOCK_PRECISION;
              printf("%lf\n", accum);
                }
#endif


static inline unsigned int get_data_cache_misses() {
#ifdef ZYNQ
    uint64_t value;
      // Read the cycle counters
      asm volatile ("MRC p15, 0, %0, c9, c13, 0\t\n": "=r"(value));
        //printf("Cycle Counter: %d\n", value);
        printf("%ld\n", value);
          // Select perfcounter 0, read from it and print value
          // asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(3));
          // Read event type
          // asm volatile ("MRC p15, 0, %0, c9, c13, 1\t\n": "=r"(value));
          // asm volatile ("MRC p15, 0, %0, c9, c13, 2\t\n": "=r"(value));
          //printf("L1 Accesses:   %d\n", value);
          // Select perfcounter 1, read from it and print value
          //asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(5));
          //asm volatile ("MRC p15, 0, %0, c9, c13, 2\t\n": "=r"(value));
          //printf("L1 Misses:     %d\n", value);
        /*
              for(int i=0;i<7;i++){
                  asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(i));
                      asm volatile ("MRC p15, 0, %0, c9, c13, 1\t\n": "=r"(value));
                          printf("perfcounter %d tracking event %d: ", i, value);
                              asm volatile ("MRC p15, 0, %0, c9, c13, 2\t\n": "=r"(value));
                                  printf("%d\n", value);
                                    }
                                    */
          return value;
#else
            return 0;
#endif
}

static inline void reset_perfcounters() {
#ifdef ZYNQ
    // 1 : enable all counters
    // 2 : reset event counters to 0
    // 4 : reset cycle counter to 0
    // 16: enables export of the events from the event bus
    uint64_t value = 1 | 2 | 4 | 16;

      // program the performance-counter control-register:
      asm volatile ("mcr p15, 0, %0, c9, c12, 0\t\n" :: "r"(value));

        // enable all counters:
        asm volatile ("MCR p15, 0, %0, c9, c12, 1\t\n" :: "r"(0x8000007f));

          // clear overflows:
          asm volatile ("MCR p15, 0, %0, c9, c12, 3\t\n" :: "r"(0x8000007f));

            // select event type to be counted:
            //    L1 Cache accesses: 0x04, tracked by perfcounter 0
            //asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(0));
            //asm volatile ("MCR p15, 0, %0, c9, c13, 1\t\n" :: "r"(0x04));
            //    L1 Cache misses:   0x03, tracked by perfcounter 1
            //asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(1));
            //asm volatile ("MCR p15, 0, %0, c9, c13, 1\t\n" :: "r"(0x03));
            //for(int i=0;i<7;i++){
              asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(0));
                  asm volatile ("MCR p15, 0, %0, c9, c13, 1\t\n" :: "r"(0x04));
                    //}
#endif
}

int check_file(FILE *fp){
    if (fp==NULL){
          fprintf(stderr, "Error opening file: %s\n", strerror(errno));
              return 0;
                }
      return 1;
}

void wait_for_the_flag(){
    FILE *fp;
      int flag = 48; // ASCII for 0
        fp = fopen("flag", "r");

          if (check_file(fp)){
                flag=fgetc(fp);
                    fclose(fp);
                        while(flag == 48){
                                fp = fopen("flag", "r");
                                      flag=fgetc(fp);
                                            fclose(fp);
                                                }
                          }
}

void set_the_flag(){
    FILE *fp;
      fp = fopen("flag", "w+");
        if (check_file(fp)){
              fprintf(fp, "1");
                  fclose(fp);
                    }
}

