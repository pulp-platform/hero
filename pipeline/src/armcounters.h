#ifndef ARM_COUNTERS_H
#define ARM_COUNTERS_H
// Copy-Paste from https://stackoverflow.com/questions/16236460/arm-cortex-a9-event-counters-return-0

// My system has 6 configurable counters and a separate Cycle Count register.
// This will contain a nice human-readable name for the configured counters.
const char* cpu_name[7] = { "", "", "", "", "", "", "CCNT" };

typedef struct {
  int reg[7];       // 6 configurables and the cycle count
} cpu_perf;


int _read_cpu_counter(int r) {
  // Read PMXEVCNTR #r
  // This is done by first writing the counter number to PMSELR and then reading PMXEVCNTR
  int ret;
  asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(r));      // Select event counter in PMSELR
  asm volatile ("MRC p15, 0, %0, c9, c13, 2\t\n" : "=r"(ret));    // Read from PMXEVCNTR
  return ret;
}

void _setup_cpu_counter(int r, int event, const char* name) {
  cpu_name[r] = name;

  // Write PMXEVTYPER #r
  // This is done by first writing the counter number to PMSELR and then writing PMXEVTYPER
  asm volatile ("MCR p15, 0, %0, c9, c12, 5\t\n" :: "r"(r));        // Select event counter in PMSELR
  asm volatile ("MCR p15, 0, %0, c9, c13, 1\t\n" :: "r"(event));    // Set the event number in PMXEVTYPER
}

void init_cpu_perf() {

  // Disable all counters for configuration (PCMCNTENCLR)
  asm volatile ("MCR p15, 0, %0, c9, c12, 2\t\n" :: "r"(0x8000000f));

  // disable counter overflow interrupts CURRENTLY ILLEGAL
  //asm volatile ("MCR p15, 0, %0, c9, c14, 2\n\t" :: "r"(0x8000000f));


  // Select which events to count in the 6 configurable counters
  // Note that both of these examples come from the list of required events.
  _setup_cpu_counter(0, 0x04, "L1DACC  ");
  _setup_cpu_counter(1, 0x03, "L1DFILL ");
  _setup_cpu_counter(2, 0x16, "L2DACC  ");
  _setup_cpu_counter(3, 0x17, "L2DFILL ");

}


void reset_cpu_perf() {

  // Disable all counters (PMCNTENCLR):
  asm volatile ("MCR p15, 0, %0, c9, c12, 2\t\n" :: "r"(0x8000000f));

  int pmcr  = 0x1    // enable counters
            | 0x2    // reset all other counters
            | 0x4    // reset cycle counter
            | 0x8    // enable "by 64" divider for CCNT.
            | 0x10;  // Export events to external monitoring

  // program the performance-counter control-register (PMCR):
  asm volatile ("MCR p15, 0, %0, c9, c12, 0\t\n" :: "r"(pmcr));

  // clear overflows (PMOVSR):
  asm volatile ("MCR p15, 0, %0, c9, c12, 3\t\n" :: "r"(0x8000000f));

  // Enable all counters (PMCNTENSET):
  asm volatile ("MCR p15, 0, %0, c9, c12, 1\t\n" :: "r"(0x8000000f));

}

cpu_perf get_cpu_perf() {
  cpu_perf ret;
  int r;

  // Read the configurable counters
  for (r=0; r<4; ++r) {
    ret.reg[r] = _read_cpu_counter(r);
		printf("%s: %d\n", cpu_name[r], ret.reg[r]);
  }

  // Read CPU cycle count from the CCNT Register
  asm volatile ("MRC p15, 0, %0, c9, c13, 0\t\n": "=r"(ret.reg[6]));
	printf("CCNT    : %d\n", ret.reg[6]);

  return ret;
}
#endif //ARM_COUNTERS_H
