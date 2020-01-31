# HERO Apps

The apps are a set of auxilliary applications for HERO and are utilities to interface PULP from the host. At the moment two applications are implemented:

## PULP Standalone
Allows running standalone applications that are compiled directly for PULP, without the involvement of the heterogeneous toolchain. 
These PULP applications do not interact with the host.

A very simple standalone application to write a value to shared memory (L3) can be created as follows.
Create a file `main.c` with contents:
```
#include "pulp.h"

int main() {
  volatile int *ptr = (int *)0x80000000;
  *ptr = 0xdeadbeef;
}
```
Create a `Makefile` with contents
```
PULP_APP = test
PULP_APP_SRCS = main.c
PULP_CFLAGS = -O3 -g

include $(PULP_SDK_INSTALL)/rules/pulp_rt.mk
```

Then source the appropriate environment script (for example `source env/exilzcu102.sh`) and run `make`. 
Afterwards the relevant binaries in `build/<chip>/test/test.l2.bin` and `build/<chip>/test/test.tcdm.bin` have to be copied to the machine and can be executed by running `pulp-standalone test`.

## PULP UART
Allows to read the UART stream from PULP on the host. After starting the application should automatically fetch the print statements from PULP. 

*NOTE: the PULP UART application does not function yet on the ZCU102, as the UART is currently not directly accessible from the PL*
