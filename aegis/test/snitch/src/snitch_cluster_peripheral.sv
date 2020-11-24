/// Exposes cluster confugration and information as memory mapped information

`include "common_cells/registers.svh"

module snitch_cluster_peripheral #(
  parameter logic [31:0] TCDMStartAddress = 32'h0,  // TCDM Start Adddress
  parameter logic [31:0] TCDMEndAddress   = 32'h0,  // TCDM End Address
  parameter type         tcdm_events_t    = logic,
  parameter logic [31:0] NrCores          = 0       // Nr of course in the cluster
) (
  input  logic                                   clk_i,
  input  logic                                   rst_i,
  input  logic [63:0]                            addr_i,
  input  logic [63:0]                            wdata_i,
  input  logic                                   write_i,
  output logic [63:0]                            rdata_o,
  input  logic [7:0]                             wstrb_i,
  output logic                                   error_o,
  input  logic                                   valid_i,
  output logic                                   ready_o,
  output logic [NrCores-1:0]                     wake_up_o,
  input  logic [ 9:0]                            cluster_hart_base_id_i,
  input  snitch_pkg::core_events_t [NrCores-1:0] core_events_i,
  input              tcdm_events_t               tcdm_events_i
);
  // peripheral address length
  localparam PLEN = $bits(snitch_pkg::cluster_peripheral_addr_e);
  logic [PLEN-1:0] addr;
  assign addr =  addr_i[PLEN-1:0];

  assign ready_o = 1'b1;

  logic [NrCores-1:0] fetch_enable_q, fetch_enable_d;
  logic [NrCores-1:0] wake_up_q, wake_up_d;
  logic [63:0] scratch_q, scratch_d;
  logic [63:0] cycle_q, cycle_d;
  // TODO(zarubaf, fschuiki) ICEBOX: Make the number of performance counters
  // configurable and usually smaller than the number of events, then allow for
  // an event mask to be used to count specific instances of an event.
  localparam int NumPerfCount = $bits(core_events_i);
  logic [NumPerfCount-1:0][31:0] perf_count_q, perf_count_d;
  tcdm_events_t tcdm_events_q;
  logic [31:0] tcdm_accessed_q, tcdm_congested_q;

  `FFSR(fetch_enable_q, fetch_enable_d, '0, clk_i, rst_i)
  `FFSR(scratch_q, scratch_d, '0, clk_i, rst_i)
  `FFSR(wake_up_q, wake_up_d, '0, clk_i, rst_i)
  `FFSR(perf_count_q, perf_count_d, '0, clk_i, rst_i)
  `FFSR(cycle_q, cycle_d, '0, clk_i, rst_i)
  `FFSR(tcdm_events_q, tcdm_events_i, '0, clk_i, rst_i)
  `FFSR(tcdm_accessed_q, tcdm_accessed_q + tcdm_events_q.inc_accessed, '0, clk_i, rst_i)
  `FFSR(tcdm_congested_q, tcdm_congested_q + tcdm_events_q.inc_congested, '0, clk_i, rst_i)

  assign wake_up_o = wake_up_q;
  assign cycle_d = cycle_q + 1;

  function automatic logic [63:0] bitlerp (logic [63:0] dst, logic [63:0] src, logic [63:0] mask);
       return (src & mask) | (dst & ~mask);
  endfunction

  always_comb begin
    automatic logic [63:0] mask;

    rdata_o = '0;
    error_o = 1'b0;
    fetch_enable_d = fetch_enable_q;
    scratch_d = scratch_q;
    wake_up_d = '0;

    mask = '0;
    for (int i = 0; i < 8; i++)
      mask[i*8+:8] = wstrb_i[i] ? '1 : '0;

    if (ready_o && valid_i) begin
      if (write_i) begin
        unique case (snitch_pkg::cluster_peripheral_addr_e'(addr))
          snitch_pkg::FetchEnableReg: begin
            fetch_enable_d = bitlerp(fetch_enable_q, wdata_i[NrCores-1:0], mask);
          end
          snitch_pkg::ScratchReg: begin
            scratch_d = bitlerp(scratch_q, wdata_i, mask);
          end
          snitch_pkg::WakeUpReg: begin
            wake_up_d = bitlerp(wake_up_q, wdata_i[NrCores-1:0], mask);
          end
          default: error_o = wstrb_i != '0;
        endcase
      end else begin
        unique case (snitch_pkg::cluster_peripheral_addr_e'(addr))
          snitch_pkg::TCDMStartAddressReg: begin
            rdata_o = TCDMStartAddress;
          end
          snitch_pkg::TCDMEndAddressReg: begin
            rdata_o = TCDMEndAddress;
          end
          snitch_pkg::NrCoresReg: begin
            // don't count the platform controller as a compute core
            rdata_o = NrCores;
          end
          snitch_pkg::FetchEnableReg: begin
            rdata_o = fetch_enable_q;
          end
          snitch_pkg::ScratchReg: begin
            rdata_o = scratch_q;
          end
          snitch_pkg::CycleCountReg: begin
            rdata_o = cycle_q;
          end
          snitch_pkg::BarrierReg: begin
            rdata_o = '0;
          end
          snitch_pkg::ClusterIdReg: begin
            rdata_o = cluster_hart_base_id_i;
          end
          snitch_pkg::TcdmAccessedReg: begin
            rdata_o = tcdm_accessed_q;
          end
          snitch_pkg::TcdmCongestedReg: begin
            rdata_o = tcdm_congested_q;
          end
          default: begin
            if (addr >= snitch_pkg::PerfCounterBase &&
                addr < snitch_pkg::PerfCounterBase + NumPerfCount * 8) begin
              rdata_o = perf_count_q[addr_i[15:0]/8];
            end else begin
              error_o = 1'b1;
            end
          end
        endcase
      end
    end
  end

  // Performance counters
  always_comb begin
    automatic logic [NumPerfCount-1:0] flat_events;
    flat_events = core_events_i;
    perf_count_d = perf_count_q;
    for (int i = 0; i < NumPerfCount; i++)
      if (flat_events[i])
        perf_count_d[i]++;
  end
endmodule
