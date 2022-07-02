#pragma once

#include <memory>       // For std::unique_ptr
#include <systemc.h>    // SystemC global header
#include <sys/stat.h>   // mkdir

#include <verilated.h>
#include <verilated_sc.h>
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
        cout << "here, klas_vlt" << endl;
        vlt_setup(argc, argv);
        tb_setup();
    }


    int gdriver_run(void) {
        cout << "enter " << __FUNCTION__ << endl;
        return -1;
    }

    int gdriver_finish(void) {
        cout << "enter " << __FUNCTION__ << endl;
        return -1;
    }


private:
    T *tb;
    SimControl<T> *sim;
    HostModel<AXIPort<uint64_t, uint64_t>> *host_model;

    sc_signal<bool> rst_ni;
    sc_signal<bool> pmu_mem_pwdn_i;
    sc_signal<uint32_t> base_addr_i;
    sc_signal<bool> test_mode_i;
    sc_signal<bool> en_sa_boot_i;
    sc_signal<uint32_t> cluster_id_i;
    sc_signal<bool> fetch_en_i;
    sc_signal<bool> eoc_o;
    sc_signal<bool> busy_o;
    sc_signal<uint32_t> ext_events_writetoken_i;
    sc_signal<uint32_t> ext_events_readpointer_o;
    sc_signal<uint32_t> ext_events_dataasync_i;
    sc_signal<bool> dma_pe_evt_ack_i;
    sc_signal<bool> dma_pe_evt_valid_o;
    sc_signal<bool> dma_pe_irq_ack_i;
    sc_signal<bool> dma_pe_irq_valid_o;
    sc_signal<bool> pf_evt_ack_i;
    sc_signal<bool> pf_evt_valid_o;
    sc_signal<uint32_t> data_slave_aw_prot_i;
    sc_signal<uint32_t> data_slave_aw_region_i;
    sc_signal<uint32_t> data_slave_aw_len_i;
    sc_signal<uint32_t> data_slave_aw_size_i;
    sc_signal<uint32_t> data_slave_aw_burst_i;
    sc_signal<bool> data_slave_aw_lock_i;
    sc_signal<uint32_t> data_slave_aw_atop_i;
    sc_signal<uint32_t> data_slave_aw_cache_i;
    sc_signal<uint32_t> data_slave_aw_qos_i;
    sc_signal<uint32_t> data_slave_aw_id_i;
    sc_signal<uint32_t> data_slave_aw_user_i;
    sc_signal<uint32_t> data_slave_aw_writetoken_i;
    sc_signal<uint32_t> data_slave_aw_readpointer_o;
    sc_signal<bool> data_slave_aw_valid_i;
    sc_signal<bool> data_slave_aw_ready_o;
    sc_signal<uint32_t> data_slave_ar_prot_i;
    sc_signal<uint32_t> data_slave_ar_region_i;
    sc_signal<uint32_t> data_slave_ar_len_i;
    sc_signal<uint32_t> data_slave_ar_size_i;
    sc_signal<uint32_t> data_slave_ar_burst_i;
    sc_signal<bool> data_slave_ar_lock_i;
    sc_signal<uint32_t> data_slave_ar_cache_i;
    sc_signal<uint32_t> data_slave_ar_qos_i;
    sc_signal<uint32_t> data_slave_ar_id_i;
    sc_signal<uint32_t> data_slave_ar_user_i;
    sc_signal<uint32_t> data_slave_ar_writetoken_i;
    sc_signal<uint32_t> data_slave_ar_readpointer_o;
    sc_signal<bool> data_slave_ar_valid_i;
    sc_signal<bool> data_slave_ar_ready_o;
    sc_signal<uint32_t> data_slave_w_strb_i;
    sc_signal<uint32_t> data_slave_w_user_i;
    sc_signal<bool> data_slave_w_last_i;
    sc_signal<uint32_t> data_slave_w_writetoken_i;
    sc_signal<uint32_t> data_slave_w_readpointer_o;
    sc_signal<bool> data_slave_w_valid_i;
    sc_signal<bool> data_slave_w_ready_o;
    sc_signal<uint32_t> data_slave_r_resp_o;
    sc_signal<bool> data_slave_r_last_o;
    sc_signal<uint32_t> data_slave_r_id_o;
    sc_signal<uint32_t> data_slave_r_user_o;
    sc_signal<uint32_t> data_slave_r_writetoken_o;
    sc_signal<uint32_t> data_slave_r_readpointer_i;
    sc_signal<bool> data_slave_r_valid_o;
    sc_signal<bool> data_slave_r_ready_i;
    sc_signal<uint32_t> data_slave_b_resp_o;
    sc_signal<uint32_t> data_slave_b_id_o;
    sc_signal<uint32_t> data_slave_b_user_o;
    sc_signal<uint32_t> data_slave_b_writetoken_o;
    sc_signal<uint32_t> data_slave_b_readpointer_i;
    sc_signal<bool> data_slave_b_valid_o;
    sc_signal<bool> data_slave_b_ready_i;
    sc_signal<uint32_t> data_master_aw_prot_o;
    sc_signal<uint32_t> data_master_aw_region_o;
    sc_signal<uint32_t> data_master_aw_len_o;
    sc_signal<uint32_t> data_master_aw_size_o;
    sc_signal<uint32_t> data_master_aw_burst_o;
    sc_signal<bool> data_master_aw_lock_o;
    sc_signal<uint32_t> data_master_aw_atop_o;
    sc_signal<uint32_t> data_master_aw_cache_o;
    sc_signal<uint32_t> data_master_aw_qos_o;
    sc_signal<uint32_t> data_master_aw_id_o;
    sc_signal<uint32_t> data_master_aw_user_o;
    sc_signal<uint32_t> data_master_aw_writetoken_o;
    sc_signal<uint32_t> data_master_aw_readpointer_i;
    sc_signal<bool> data_master_aw_valid_o;
    sc_signal<bool> data_master_aw_ready_i;
    sc_signal<uint32_t> data_master_ar_prot_o;
    sc_signal<uint32_t> data_master_ar_region_o;
    sc_signal<uint32_t> data_master_ar_len_o;
    sc_signal<uint32_t> data_master_ar_size_o;
    sc_signal<uint32_t> data_master_ar_burst_o;
    sc_signal<bool> data_master_ar_lock_o;
    sc_signal<uint32_t> data_master_ar_cache_o;
    sc_signal<uint32_t> data_master_ar_qos_o;
    sc_signal<uint32_t> data_master_ar_id_o;
    sc_signal<uint32_t> data_master_ar_user_o;
    sc_signal<uint32_t> data_master_ar_writetoken_o;
    sc_signal<uint32_t> data_master_ar_readpointer_i;
    sc_signal<bool> data_master_ar_valid_o;
    sc_signal<bool> data_master_ar_ready_i;
    sc_signal<uint32_t> data_master_w_strb_o;
    sc_signal<uint32_t> data_master_w_user_o;
    sc_signal<bool> data_master_w_last_o;
    sc_signal<uint32_t> data_master_w_writetoken_o;
    sc_signal<uint32_t> data_master_w_readpointer_i;
    sc_signal<bool> data_master_w_valid_o;
    sc_signal<bool> data_master_w_ready_i;
    sc_signal<uint32_t> data_master_r_resp_i;
    sc_signal<bool> data_master_r_last_i;
    sc_signal<uint32_t> data_master_r_id_i;
    sc_signal<uint32_t> data_master_r_user_i;
    sc_signal<uint32_t> data_master_r_writetoken_i;
    sc_signal<uint32_t> data_master_r_readpointer_o;
    sc_signal<bool> data_master_r_valid_i;
    sc_signal<bool> data_master_r_ready_o;
    sc_signal<uint32_t> data_master_b_resp_i;
    sc_signal<uint32_t> data_master_b_id_i;
    sc_signal<uint32_t> data_master_b_user_i;
    sc_signal<uint32_t> data_master_b_writetoken_i;
    sc_signal<uint32_t> data_master_b_readpointer_o;
    sc_signal<bool> data_master_b_valid_i;
    sc_signal<bool> data_master_b_ready_o;
    sc_signal<vluint64_t> data_slave_aw_addr_i;
    sc_signal<vluint64_t> data_slave_ar_addr_i;
    sc_signal<vluint64_t> data_slave_w_data_i;
    sc_signal<vluint64_t> data_slave_r_data_o;
    sc_signal<vluint64_t> data_master_aw_addr_o;
    sc_signal<vluint64_t> data_master_ar_addr_o;
    sc_signal<vluint64_t> data_master_w_data_o;
    sc_signal<vluint64_t> data_master_r_data_i;

    //     <AW_t    , STRB_T  >
    AXIPort<vluint64_t, vluint64_t> axi_data_slave;
    AXIPort<vluint64_t, vluint64_t> axi_data_master;

private:
    int vlt_setup(int argc, char *argv[]) {
        cout << "enter " << __FUNCTION__ << endl;
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
        cout << "enter " << __FUNCTION__ << endl;

        tb = new T("tb");
        sim = new SimControl<T>(tb, VCD_FILE);

        cout << "here, 1" << endl;
        // Define clocks
        clk     = new sc_clock("clk_i"    , 10, SC_NS, 0.5, 3, SC_NS, true);
        ref_clk = new sc_clock("ref_clk_i",  2, SC_NS, 0.5, 2, SC_NS, true);
        cout << "here, 2" << endl;

#ifdef VERILATOR_HAS_TRACE
    cout << "defined" << endl;
#else
    cout << "non-defined" << endl;
#endif
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

        cout << "here, 3, " << endl;

        aw_prot.write(*(axi_data_slave.aw_prot)); tb->data_slave_aw_prot_i(aw_prot);

        axi_data_slave.AXIPort_init();
        AXI_MASTER_PORT_ASSIGN(tb, data_slave,  axi_data_slave ); // host to dut
        cout << "here, 4" << endl;
        axi_data_master.AXIPort_init();
        AXI_SLAVE_PORT_ASSIGN (tb, data_master, axi_data_master); // dut to external memory
        cout << "here, 5" << endl;

        //host_model = new HostModel<AXIPort<uint64_t, uint64_t>>(axi_data_slave);

        //sim->add_module(*host_model);
        sim->reset();
        cout << "here, 6" << endl;

        return 0;
    }
};


