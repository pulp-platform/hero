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

using namespace std;

int sc_main(int argc, char* argv[]) {
    // Prevent unused variable warnings
    if (false && argc && argv) {}

    cout << "Verilator on" << endl;
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
    cout << "Clock defined" << endl;

    // Define interconnect
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
    sc_signal<uint64_t> data_slave_aw_addr_i;
    sc_signal<uint64_t> data_slave_ar_addr_i;
    sc_signal<uint64_t> data_slave_w_data_i;
    sc_signal<uint64_t> data_slave_r_data_o;
    sc_signal<uint64_t> data_master_aw_addr_o;
    sc_signal<uint64_t> data_master_ar_addr_o;
    sc_signal<uint64_t> data_master_w_data_o;
    sc_signal<uint64_t> data_master_r_data_i;

    // Construct the Verilated model, from inside Vtop.h
    // Using unique_ptr is similar to "Vtop* top = new Vtop" then deleting at end
    const std::unique_ptr<Vtop> top{new Vtop{"top"}};

    // Attach Vtop's signals to this upper model
    top->clk_i(clk_i);
    top->ref_clk_i(ref_clk_i);
    top->rst_ni(rst_ni);
    top->pmu_mem_pwdn_i(pmu_mem_pwdn_i);
    top->base_addr_i(base_addr_i);
    top->test_mode_i(test_mode_i);
    top->en_sa_boot_i(en_sa_boot_i);
    top->cluster_id_i(cluster_id_i);
    top->fetch_en_i(fetch_en_i);
    top->eoc_o(eoc_o);
    top->busy_o(busy_o);
    top->ext_events_writetoken_i(ext_events_writetoken_i);
    top->ext_events_readpointer_o(ext_events_readpointer_o);
    top->ext_events_dataasync_i(ext_events_dataasync_i);
    top->dma_pe_evt_ack_i(dma_pe_evt_ack_i);
    top->dma_pe_evt_valid_o(dma_pe_evt_valid_o);
    top->dma_pe_irq_ack_i(dma_pe_irq_ack_i);
    top->dma_pe_irq_valid_o(dma_pe_irq_valid_o);
    top->pf_evt_ack_i(pf_evt_ack_i);
    top->pf_evt_valid_o(pf_evt_valid_o);
    top->data_slave_aw_prot_i(data_slave_aw_prot_i);
    top->data_slave_aw_region_i(data_slave_aw_region_i);
    top->data_slave_aw_len_i(data_slave_aw_len_i);
    top->data_slave_aw_size_i(data_slave_aw_size_i);
    top->data_slave_aw_burst_i(data_slave_aw_burst_i);
    top->data_slave_aw_lock_i(data_slave_aw_lock_i);
    top->data_slave_aw_atop_i(data_slave_aw_atop_i);
    top->data_slave_aw_cache_i(data_slave_aw_cache_i);
    top->data_slave_aw_qos_i(data_slave_aw_qos_i);
    top->data_slave_aw_id_i(data_slave_aw_id_i);
    top->data_slave_aw_user_i(data_slave_aw_user_i);
    top->data_slave_aw_writetoken_i(data_slave_aw_writetoken_i);
    top->data_slave_aw_readpointer_o(data_slave_aw_readpointer_o);
    top->data_slave_aw_valid_i(data_slave_aw_valid_i);
    top->data_slave_aw_ready_o(data_slave_aw_ready_o);
    top->data_slave_ar_prot_i(data_slave_ar_prot_i);
    top->data_slave_ar_region_i(data_slave_ar_region_i);
    top->data_slave_ar_len_i(data_slave_ar_len_i);
    top->data_slave_ar_size_i(data_slave_ar_size_i);
    top->data_slave_ar_burst_i(data_slave_ar_burst_i);
    top->data_slave_ar_lock_i(data_slave_ar_lock_i);
    top->data_slave_ar_cache_i(data_slave_ar_cache_i);
    top->data_slave_ar_qos_i(data_slave_ar_qos_i);
    top->data_slave_ar_id_i(data_slave_ar_id_i);
    top->data_slave_ar_user_i(data_slave_ar_user_i);
    top->data_slave_ar_writetoken_i(data_slave_ar_writetoken_i);
    top->data_slave_ar_readpointer_o(data_slave_ar_readpointer_o);
    top->data_slave_ar_valid_i(data_slave_ar_valid_i);
    top->data_slave_ar_ready_o(data_slave_ar_ready_o);
    top->data_slave_w_strb_i(data_slave_w_strb_i);
    top->data_slave_w_user_i(data_slave_w_user_i);
    top->data_slave_w_last_i(data_slave_w_last_i);
    top->data_slave_w_writetoken_i(data_slave_w_writetoken_i);
    top->data_slave_w_readpointer_o(data_slave_w_readpointer_o);
    top->data_slave_w_valid_i(data_slave_w_valid_i);
    top->data_slave_w_ready_o(data_slave_w_ready_o);
    top->data_slave_r_resp_o(data_slave_r_resp_o);
    top->data_slave_r_last_o(data_slave_r_last_o);
    top->data_slave_r_id_o(data_slave_r_id_o);
    top->data_slave_r_user_o(data_slave_r_user_o);
    top->data_slave_r_writetoken_o(data_slave_r_writetoken_o);
    top->data_slave_r_readpointer_i(data_slave_r_readpointer_i);
    top->data_slave_r_valid_o(data_slave_r_valid_o);
    top->data_slave_r_ready_i(data_slave_r_ready_i);
    top->data_slave_b_resp_o(data_slave_b_resp_o);
    top->data_slave_b_id_o(data_slave_b_id_o);
    top->data_slave_b_user_o(data_slave_b_user_o);
    top->data_slave_b_writetoken_o(data_slave_b_writetoken_o);
    top->data_slave_b_readpointer_i(data_slave_b_readpointer_i);
    top->data_slave_b_valid_o(data_slave_b_valid_o);
    top->data_slave_b_ready_i(data_slave_b_ready_i);
    top->data_master_aw_prot_o(data_master_aw_prot_o);
    top->data_master_aw_region_o(data_master_aw_region_o);
    top->data_master_aw_len_o(data_master_aw_len_o);
    top->data_master_aw_size_o(data_master_aw_size_o);
    top->data_master_aw_burst_o(data_master_aw_burst_o);
    top->data_master_aw_lock_o(data_master_aw_lock_o);
    top->data_master_aw_atop_o(data_master_aw_atop_o);
    top->data_master_aw_cache_o(data_master_aw_cache_o);
    top->data_master_aw_qos_o(data_master_aw_qos_o);
    top->data_master_aw_id_o(data_master_aw_id_o);
    top->data_master_aw_user_o(data_master_aw_user_o);
    top->data_master_aw_writetoken_o(data_master_aw_writetoken_o);
    top->data_master_aw_readpointer_i(data_master_aw_readpointer_i);
    top->data_master_aw_valid_o(data_master_aw_valid_o);
    top->data_master_aw_ready_i(data_master_aw_ready_i);
    top->data_master_ar_prot_o(data_master_ar_prot_o);
    top->data_master_ar_region_o(data_master_ar_region_o);
    top->data_master_ar_len_o(data_master_ar_len_o);
    top->data_master_ar_size_o(data_master_ar_size_o);
    top->data_master_ar_burst_o(data_master_ar_burst_o);
    top->data_master_ar_lock_o(data_master_ar_lock_o);
    top->data_master_ar_cache_o(data_master_ar_cache_o);
    top->data_master_ar_qos_o(data_master_ar_qos_o);
    top->data_master_ar_id_o(data_master_ar_id_o);
    top->data_master_ar_user_o(data_master_ar_user_o);
    top->data_master_ar_writetoken_o(data_master_ar_writetoken_o);
    top->data_master_ar_readpointer_i(data_master_ar_readpointer_i);
    top->data_master_ar_valid_o(data_master_ar_valid_o);
    top->data_master_ar_ready_i(data_master_ar_ready_i);
    top->data_master_w_strb_o(data_master_w_strb_o);
    top->data_master_w_user_o(data_master_w_user_o);
    top->data_master_w_last_o(data_master_w_last_o);
    top->data_master_w_writetoken_o(data_master_w_writetoken_o);
    top->data_master_w_readpointer_i(data_master_w_readpointer_i);
    top->data_master_w_valid_o(data_master_w_valid_o);
    top->data_master_w_ready_i(data_master_w_ready_i);
    top->data_master_r_resp_i(data_master_r_resp_i);
    top->data_master_r_last_i(data_master_r_last_i);
    top->data_master_r_id_i(data_master_r_id_i);
    top->data_master_r_user_i(data_master_r_user_i);
    top->data_master_r_writetoken_i(data_master_r_writetoken_i);
    top->data_master_r_readpointer_o(data_master_r_readpointer_o);
    top->data_master_r_valid_i(data_master_r_valid_i);
    top->data_master_r_ready_o(data_master_r_ready_o);
    top->data_master_b_resp_i(data_master_b_resp_i);
    top->data_master_b_id_i(data_master_b_id_i);
    top->data_master_b_user_i(data_master_b_user_i);
    top->data_master_b_writetoken_i(data_master_b_writetoken_i);
    top->data_master_b_readpointer_o(data_master_b_readpointer_o);
    top->data_master_b_valid_i(data_master_b_valid_i);
    top->data_master_b_ready_o(data_master_b_ready_o);
    top->data_slave_aw_addr_i(data_slave_aw_addr_i);
    top->data_slave_ar_addr_i(data_slave_ar_addr_i);
    top->data_slave_w_data_i(data_slave_w_data_i);
    top->data_slave_r_data_o(data_slave_r_data_o);
    top->data_master_aw_addr_o(data_master_aw_addr_o);
    top->data_master_ar_addr_o(data_master_ar_addr_o);
    top->data_master_w_data_o(data_master_w_data_o);
    top->data_master_r_data_i(data_master_r_data_i);
    cout << "port connected" << endl;

    // You must do one evaluation before enabling waves, in order to allow
    // SystemC to interconnect everything for testing.
    sc_start(1, SC_NS);
    cout << "start" << endl;

#if VM_TRACE
    // If verilator was invoked with --trace argument,
    // and if at run time passed the +trace argument, turn on tracing
    VerilatedVcdSc* tfp = nullptr;
    const char* flag = Verilated::commandArgsPlusMatch("trace");
    cout << "Trace on" << endl;
    if (flag && 0 == strcmp(flag, "+trace")) {
        cout << "Enabling waves into logs/vlt_dump.vcd...\n";
        tfp = new VerilatedVcdSc;
        top->trace(tfp, 99);  // Trace 99 levels of hierarchy
        Verilated::mkdir("logs");
        tfp->open("logs/vlt_dump.vcd");
    }
#endif

    int a = 0;
    // Simulate until $finish
    while (!Verilated::gotFinish()) {
        cout << "running" << endl;
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
        if(a++ > 10) break;
    }

    // Final model cleanup
    top->final();
    cout << "finished" << endl;

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
