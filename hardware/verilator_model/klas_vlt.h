#pragma once

#include <iostream>
#include <memory>       // For std::unique_ptr

#include <verilated.h>
#include <verilated_vcd_c.h>

#include "AXIDriver.hpp"
#include "SimControl.hpp"
#include "HostModel.hpp"

#define VCD_FILE    "l1_dump.vcd"

using namespace KLAS_SIM;
using namespace std;

template<class T>
class klas_vlt {
public:
    klas_vlt(int argc, char *argv[]) {
        cout << "here, klas_vlt" << endl;
        vlt_setup(argc, argv);
        tb_setup();
    }


    int gdriver_run(void) {
        cout << "enter " << __FUNCTION__ << endl;
        sim->run_all(); // main loop

        return 0;
    }

    int gdriver_finish(void) {
        cout << "enter " << __FUNCTION__ << endl;
        return -1;
    }

    //double sc_time_stamp() {   // Called by $time in Verilog
    //    return sim->time();
    //}


private:
    VerilatedContext *contextp;
    T *tb;
    SimControl<T> *sim;
    HostModel<AXIPort<uint64_t, uint8_t>> *host_model;

    uint8_t *pmu_mem_pwdn_i;
    uint8_t *base_addr_i;
    uint8_t *test_mode_i;
    uint8_t *en_sa_boot_i;
    uint8_t *cluster_id_i;
    uint8_t *fetch_en_i;
    uint8_t *eoc_o;
    uint8_t *busy_o;
    uint8_t *ext_events_writetoken_i;
    uint8_t *ext_events_readpointer_o;
    uint8_t *ext_events_dataasync_i;
    uint8_t *dma_pe_evt_ack_i;
    uint8_t *dma_pe_evt_valid_o;
    uint8_t *dma_pe_irq_ack_i;
    uint8_t *dma_pe_irq_valid_o;
    uint8_t *pf_evt_ack_i;
    uint8_t *pf_evt_valid_o;

    //     <AW_t    , STRB_T  >
    AXIPort<uint64_t, uint8_t> axi_data_slave;
    AXIPort<uint64_t, uint8_t> axi_data_master;

private:
    int vlt_setup(int argc, char *argv[]) {
        cout << "enter " << __FUNCTION__ << endl;

        // Prevent unused variable warnings
        if (false && argc && argv) {}

        // Create logs/ directory in case we have traces to put under it
        Verilated::mkdir("logs");

        // Construct a VerilatedContext to hold simulation time, etc.
        // Multiple modules (made later below with Vtop) may share the same
        // context to share time, or modules may have different contexts if
        // they should be independent from each other.

        contextp = new VerilatedContext;
        // Do not instead make Vtop as a file-scope static variable, as the
        // "C++ static initialization order fiasco" may cause a crash

        // Set debug level, 0 is off, 9 is highest presently used
        // May be overridden by commandArgs argument parsing
        contextp->debug(0);

        // Randomization reset policy
        // May be overridden by commandArgs argument parsing
        contextp->randReset(2);

        // Verilator must compute traced signals
        contextp->traceEverOn(true);

        // Pass arguments so Verilated code can see them, e.g. $value$plusargs
        // This needs to be called before you create any model
        contextp->commandArgs(argc, argv);

        return 0;
    }

    int tb_setup(void) {
        cout << "enter " << __FUNCTION__ << endl;

        tb = new T(contextp, "tb");
        sim = new SimControl<T>(tb, VCD_FILE);

#ifdef VERILATOR_HAS_TRACE
    cout << "trace is defined" << endl;
#else
    cout << "trace is not defined" << endl;
#endif
        // connection dut io
        pmu_mem_pwdn_i             = &(tb->pmu_mem_pwdn_i          );
        base_addr_i                = &(tb->base_addr_i             );
        test_mode_i                = &(tb->test_mode_i             );
        en_sa_boot_i               = &(tb->en_sa_boot_i            );
        cluster_id_i               = &(tb->cluster_id_i            );
        fetch_en_i                 = &(tb->fetch_en_i              );
        eoc_o                      = &(tb->eoc_o                   );
        busy_o                     = &(tb->busy_o                  );
        ext_events_writetoken_i    = &(tb->ext_events_writetoken_i );
        ext_events_readpointer_o   = &(tb->ext_events_readpointer_o);
        ext_events_dataasync_i     = &(tb->ext_events_dataasync_i  );
        dma_pe_evt_ack_i           = &(tb->dma_pe_evt_ack_i        );
        dma_pe_evt_valid_o         = &(tb->dma_pe_evt_valid_o      );
        dma_pe_irq_ack_i           = &(tb->dma_pe_irq_ack_i        );
        dma_pe_irq_valid_o         = &(tb->dma_pe_irq_valid_o      );
        pf_evt_ack_i               = &(tb->pf_evt_ack_i            );
        pf_evt_valid_o             = &(tb->pf_evt_valid_o          );

        AXI_MASTER_PORT_ASSIGN(tb, data_slave,  &axi_data_slave ); // host to dut
        AXI_SLAVE_PORT_ASSIGN (tb, data_master, &axi_data_master); // dut to external memory

        host_model = new HostModel<AXIPort<uint64_t, uint8_t>>(axi_data_slave);

        sim->add_module(*host_model);
        sim->reset();

        return 0;
    }
};


