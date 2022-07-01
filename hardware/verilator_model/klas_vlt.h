#pragma once

#include <memory>       // For std::unique_ptr
#include <systemc.h>    // SystemC global header
#include <sys/stat.h>   // mkdir

#include <verilated.h>
#include <verilated_vcd_sc.h>

#include "AXIDriver.hpp"
#include "SimControl.hpp"
#include "HostModel.hpp"

#define VCD_FILE    "l1_dump.vcd"

using namespace KLAS_SIM;
using namespace std;

template<class T>
class klas_vlt {
public:
    sc_clock *clk    ;
    sc_clock *ref_clk;

public:
    klas_vlt(int argc, char *argv[]) {
        vlt_setup(argc, argv);
        tb_setup();
    }


    int gdriver_run(void) {
        cout << "here, gdriver_run" << endl;
        return -1;
    }

    int gdriver_finish(void) {
        cout << "here, gdriver_finish" << endl;
        return -1;
    }


private:
    T *tb;
    SimControl<T> *sim;
    HostModel<AXIPort<uint64_t, uint64_t>> *host_model;

    sc_signal<bool    > rst_ni;
    sc_signal<bool    > pmu_mem_pwdn_i;
    sc_signal<uint32_t> base_addr_i;
    sc_signal<bool    > test_mode_i;
    sc_signal<bool    > en_sa_boot_i;
    sc_signal<uint32_t> cluster_id_i;
    sc_signal<bool    > fetch_en_i;
    sc_signal<bool    > eoc_o;
    sc_signal<bool    > busy_o;
    sc_signal<uint32_t> ext_events_writetoken_i;
    sc_signal<uint32_t> ext_events_readpointer_o;
    sc_signal<uint32_t> ext_events_dataasync_i;
    sc_signal<bool    > dma_pe_evt_ack_i;
    sc_signal<bool    > dma_pe_evt_valid_o;
    sc_signal<bool    > dma_pe_irq_ack_i;
    sc_signal<bool    > dma_pe_irq_valid_o;
    sc_signal<bool    > pf_evt_ack_i;
    sc_signal<bool    > pf_evt_valid_o;

    //     <AW_t    , STRB_T  >
    AXIPort<uint64_t, uint64_t> axi_data_slave;
    AXIPort<uint64_t, uint64_t> axi_data_master;

private:
    int vlt_setup(int argc, char *argv[]) {
        // Pass arguments so Verilated code can see them, e.g. $value$plusargs
        // This needs to be called before you create any model
        Verilated::commandArgs(argc, argv);

        Verilated::mkdir("logs"); // Create logs/ directory in case we have traces to put under it
        Verilated::debug(0); // Set debug level, 0 is off, 9 is highest presently used
        Verilated::randReset(2); // Randomization reset policy

        // General logfile
        ios::sync_with_stdio();

        return 0;
    }

    int tb_setup(void) {
        tb = new T("tb");
        sim = new SimControl<T>(tb, VCD_FILE);

        // Define clocks
        clk     = new sc_clock("clk_i"    , 10, SC_NS, 0.5, 3, SC_NS, true);
        ref_clk = new sc_clock("ref_clk_i",  2, SC_NS, 0.5, 2, SC_NS, true);

        // connection dut io
        tb->clk_i                      (*clk                       );
        tb->ref_clk_i                  (*ref_clk                   );
        tb->pmu_mem_pwdn_i             (pmu_mem_pwdn_i             ); // TODO
        tb->base_addr_i                (base_addr_i                ); // TODO
        tb->test_mode_i                (test_mode_i                ); // TODO
        tb->en_sa_boot_i               (en_sa_boot_i               ); // TODO
        tb->cluster_id_i               (cluster_id_i               ); // TODO
        tb->fetch_en_i                 (fetch_en_i                 ); // TODO
        tb->eoc_o                      (eoc_o                      ); // TODO
        tb->busy_o                     (busy_o                     ); // TODO
        tb->ext_events_writetoken_i    (ext_events_writetoken_i    ); // TODO
        tb->ext_events_readpointer_o   (ext_events_readpointer_o   ); // TODO
        tb->ext_events_dataasync_i     (ext_events_dataasync_i     ); // TODO
        tb->dma_pe_evt_ack_i           (dma_pe_evt_ack_i           ); // TODO
        tb->dma_pe_evt_valid_o         (dma_pe_evt_valid_o         ); // TODO
        tb->dma_pe_irq_ack_i           (dma_pe_irq_ack_i           ); // TODO
        tb->dma_pe_irq_valid_o         (dma_pe_irq_valid_o         ); // TODO
        tb->pf_evt_ack_i               (pf_evt_ack_i               ); // TODO
        tb->pf_evt_valid_o             (pf_evt_valid_o             ); // TODO

        AXI_MASTER_PORT_ASSIGN(tb, data_slave,  &axi_data_slave ); // host to dut
        AXI_SLAVE_PORT_ASSIGN (tb, data_master, &axi_data_master); // dut to external memory

        //host_model = new HostModel<AXIPort<uint64_t, uint64_t>>(axi_data_slave);

        //sim->add_module(*host_model);
        sim->reset();

        return 0;
    }
};


