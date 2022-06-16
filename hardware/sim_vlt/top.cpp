// For std::unique_ptr
#include <memory>

// SystemC global header
#include <systemc.h>

// Include common routines
#include <verilated.h>
#if VM_TRACE
#include <verilated_vcd_sc.h>
#endif

#include <sys/stat.h>  // mkdir

// Include model header, generated from Verilating "top.v"
#include "Vtop.h"

int top(int argc, char* argv[]) {
    // Prevent unused variable warnings
    if (false && argc && argv) {}

    Verilated::mkdir("logs"); // Create logs/ directory in case we have traces to put under it
    Verilated::debug(0); // Set debug level, 0 is off, 9 is highest presently used
    Verilated::randReset(2); // Randomization reset policy

#if VM_TRACE
    // Before any evaluation, need to know to calculate those signals only used for tracing
    Verilated::traceEverOn(true);
#endif

    // Pass arguments so Verilated code can see them, e.g. $value$plusargs
    // This needs to be called before you create any model
    Verilated::commandArgs(argc, argv);

    // General logfile
    ios::sync_with_stdio();

    // Define clocks
    sc_clock clk_i    {"clk_i"    ,  1, SC_NS, 0.5, 3, SC_NS, true};
    sc_clock ref_clk_i{"ref_clk_i", 20, SC_NS, 0.5, 2, SC_NS, true};

    // Define interconnect
    sc_signal<bool> rst_ni;
    sc_signal<sc_bv<4>> base_addr_i;

    // Construct the Verilated model, from inside Vtop.h
    // Using unique_ptr is similar to "Vtop* top = new Vtop" then deleting at end
    const std::unique_ptr<Vtop> top{new Vtop{"top"}};

    // Attach Vtop's signals to this upper model
    top->clk_i(clk_i);
    top->ref_clk_i(ref_clk_i);
    top->rst_ni(rst_ni);
    top->base_addr_i(base_addr_i);

    // You must do one evaluation before enabling waves, in order to allow
    // SystemC to interconnect everything for testing.
    sc_start(1, SC_NS);

#if VM_TRACE
    // If verilator was invoked with --trace argument,
    // and if at run time passed the +trace argument, turn on tracing
    VerilatedVcdSc* tfp = nullptr;
    const char* flag = Verilated::commandArgsPlusMatch("trace");
    if (flag && 0 == strcmp(flag, "+trace")) {
        cout << "Enabling waves into logs/vlt_dump.vcd...\n";
        tfp = new VerilatedVcdSc;
        top->trace(tfp, 99);  // Trace 99 levels of hierarchy
        Verilated::mkdir("logs");
        tfp->open("logs/vlt_dump.vcd");
    }
#endif

    // Simulate until $finish
    while (!Verilated::gotFinish()) {
#if VM_TRACE
        // Flush the wave files each cycle so we can immediately see the output
        // Don't do this in "real" programs, do it in an abort() handler instead
        if (tfp) tfp->flush();
#endif

        // Apply inputs
        if (sc_time_stamp() > sc_time(1, SC_NS) && sc_time_stamp() < sc_time(10, SC_NS)) {
            rst_ni = !1;  // Assert reset
        } else {
            rst_ni = !0;  // Deassert reset
        }

        // Simulate 1ns
        sc_start(1, SC_NS);
    }

    // Final model cleanup
    top->final();

    // Close trace if opened
#if VM_TRACE
    if (tfp) {
        tfp->close();
        tfp = nullptr;
    }
#endif

    // Coverage analysis (calling write only after the test is known to pass)
#if VM_COVERAGE
    Verilated::mkdir("logs");
    VerilatedCov::write("logs/coverage.dat");
#endif

    // Return good completion status
    return 0;
}
