#pragma once

#define VM_TRACE 1

#include <iostream>
#include <memory>      // For std::unique_ptr
#include <systemc.h>
#include <sys/stat.h>  // mkdir
#include <verilated.h>

#include <svdpi.h>
#include <vpi_user.h>

#if VM_TRACE
#include <verilated_vcd_sc.h>
#endif

#include "klas_dpi.h"

using namespace std;

template<class T>
class klas_vlt {
public:
    klas_vlt(int argc, char *argv[]) {
        vlt_setup(argc, argv);
        tb_setup();
    }

    ~klas_vlt(void) {
        top->final(); // Final model cleanup

#if VM_TRACE
        // Close trace if opened
        tfp->flush();
        tfp->close();
        tfp = nullptr;
#endif
    }

    int klas_run(void) {
        cout << "enter " << __FUNCTION__ << endl;
        uint32_t    word;

        write_word(0x000, 0x900dc0de);
        write_word(0x100, 0x900dc0de);
        sc_start(100, SC_NS);

        read_word(0x000, &word);
        read_word(0x100, &word);
        sc_start(100, SC_NS);

#if VM_TRACE
        tfp->flush();
#endif
        return 0;
    }


private:
#if VM_TRACE
    VerilatedVcdSc* tfp ;
#endif

    T *top;

    sc_clock            *clk;
    sc_clock            *ref_clk;
    sc_signal<bool>     resetn;

private:
    int vlt_setup(int argc, char *argv[]) {
        cout << "enter " << __FUNCTION__ << endl;

        // Prevent unused variable warnings
        if (false && argc && argv) {}

        // Create logs/ directory in case we have traces to put under it
        Verilated::mkdir("logs");

        // Set debug level, 0 is off, 9 is highest presently used
        // May be overridden by commandArgs argument parsing
        Verilated::debug(0);

        // Randomization reset policy
        // May be overridden by commandArgs argument parsing
        Verilated::randReset(2);

#if VM_TRACE
        // Before any evaluation, need to know to calculate those signals only used for tracing
        Verilated::traceEverOn(true);
#endif
 
        // Pass arguments so Verilated code can see them, e.g. $value$plusargs
        // This needs to be called before you create any model
        Verilated::commandArgs(argc, argv);

        // General logfile
        ios::sync_with_stdio();

        return 0;
    }

    int tb_setup(void) {
        cout << "enter " << __FUNCTION__ << endl;

        top     = new T("top");
        clk     = new sc_clock("clk"    , 1 , SC_NS);
        ref_clk = new sc_clock("ref_clk", 28, SC_NS);

        // set DPI task/function hier
        svSetScope(svGetScopeFromName("top.top"));

        // connection top io
        top->clk_i      (*clk       );
        top->ref_clk_i  (*ref_clk   );
        top->rst_ni     (resetn     );
    
        sc_start(1, SC_NS);

#if VM_TRACE
        // If verilator was invoked with --trace argument,
        // and if at run time passed the +trace argument, turn on tracing
        tfp = nullptr;
        const char* flag = Verilated::commandArgsPlusMatch("trace");
        if (flag && 0 == strcmp(flag, "+trace")) {
            cout << "Enabling waves into logs/vlt_dump.vcd...\n";
            tfp = new VerilatedVcdSc;
            top->trace(tfp, 99);  // Trace 99 levels of hierarchy
            Verilated::mkdir("logs");
            tfp->open("logs/vlt_dump.vcd");
        }
#endif

        // Apply inputs
       while(sc_time_stamp() > sc_time(0, SC_NS) && sc_time_stamp() < sc_time(10, SC_NS)) {
            resetn = !1;  // Assert reset
            sc_start(1, SC_NS);
        }
        resetn = !0;  // Deassert reset

        // Simulate 100ns
        sc_start(100, SC_NS);

#if VM_TRACE
        tfp->flush();
#endif

        return 0;
    }

};


