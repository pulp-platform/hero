// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Company:        Multitherman Laboratory @ DEIS - University of Bologna     //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Davide Rossi - davide.rossi@unibo.it                       //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Stefan Mach - smach@iis.ee.ethz.ch                         //
//                                                                            //
// Create Date:    13/02/2013                                                 //
// Design Name:    ULPSoC                                                     //
// Module Name:    ulpcluster_top                                             //
// Project Name:   ULPSoC                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    ULPSoC cluster                                             //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - Added DVS-DVSE support for memories                        //
// Revision v0.3 - Cleand Code, added non-blocking assign in the always_ff    //
// Revision v0.4 - Updated the address range from [4:3] to[3:2]               //
// Revision v0.5 - Restored Back Addr range [4:3], because of TB issues       //
// Revision v0.6 - 29/05/15 : removed DVS-DVSE, added HS,LS,RM,WM             //
//                 LS is default 1, other are '0 by default                   //
// Revision v?   - Added fregfile_disable to the cluster control register     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Memory Map
//
// 0x000:        EoC. Write to bit 0 sets the eoc signal
// 0x008:        Fetch Enable. Each core has its own bit, starts from LSB
// 0x010:        Event. Bit 0 triggers an event. Usually not connected
// 0x018:        Cluster Config. RM, WM, HS, LS, HWPE_SEL, FREGFILE_DIS
// 0x020:        Cluster Clock Gate. Bit 0 enables it
// 0x028:        Debug Status/Resume. Each core has its own bit, starts from LSB
//               On read: Bit is set when core is halted
//               On write: Resume core x when bit x is set
// 0x038:        Debug Halt Mask. Each core has its own bit, starts from LSB
//               When bit is set, core will be part of mask group and stopped
//               when one of the members of the group stops
// 0x040-0x07F:  Boot Addresses. Each core has its own 32-bit boot address
// 0x80:         TCDM arbitration configuration CH0 (CORE)
// 0x88:         TCDM arbitration configuration CH1 (DMA HWCE)
////////////////////////////////////////////////////////////////////////////////

module cluster_control_unit
#(
    parameter NB_CORES      = 4,
    parameter PER_ID_WIDTH  = 5,
    parameter ROM_BOOT_ADDR = 32'h1A000000,
    parameter BOOT_ADDR     = 32'h1C000000
)
(
    input logic                       clk_i,
    input logic                       rst_ni,
    input logic                       en_sa_boot_i,
    input logic                       fetch_en_i,
    XBAR_PERIPH_BUS.Slave             speriph_slave,

    output logic                      event_o,
    output logic                      eoc_o,

    output logic                      cluster_cg_en_o,

    output logic                      hwpe_sel_o,
    output logic                      hwpe_en_o,

    output logic                      fregfile_disable_o,

    input  logic [NB_CORES-1:0]       core_halted_i,  // cores are in halted mode (which means debugging)
    output logic [NB_CORES-1:0]       core_halt_o,    // halt the core
    output logic [NB_CORES-1:0]       core_resume_o,  // resume the core

    output logic [NB_CORES-1:0]       fetch_enable_o,
    output logic [NB_CORES-1:0][31:0] boot_addr_o,
    output logic [1:0]                TCDM_arb_policy_o
);

  localparam OFFSET_1      = 4; // It was RM
  localparam OFFSET_2      = 4; // It was WM

  logic                               rvalid_q, rvalid_n;
  logic [PER_ID_WIDTH-1:0]            id_q, id_n;
  logic [31:0]                        rdata_q, rdata_n;
  logic [NB_CORES-1:0]                fetch_en_q, fetch_en_n;

  logic [NB_CORES-1:0]                dbg_halt_mask_q, dbg_halt_mask_n;
  logic                               core_halted_any_q, core_halted_any_n;

  logic                               eoc_n;
  logic                               event_n;

  logic                               hwpe_sel_n;
  logic                               hwpe_en_n;

  logic                               fregfile_disable_n;

  logic [NB_CORES-1:0][31:0]          boot_addr_n;

  logic [1:0]                         fetch_en_sync;
  logic                               start_fetch;
  logic                               start_boot;
  logic                               cluster_cg_en_n;

  logic [1:0]                         TCDM_arb_policy_n;

  logic                               core_halt_rising_edge;

  enum logic [1:0] { RESET, BOOT, WAIT_FETCH, LIMBO } boot_cs, boot_ns;

  assign fetch_enable_o  = fetch_en_q;

  always_comb
  begin
    boot_ns     = boot_cs;
    start_boot  = 1'b0;
    start_fetch = 1'b0;

    case (boot_cs)
      RESET: begin
        boot_ns = BOOT;
      end

      BOOT: begin
        boot_ns = WAIT_FETCH;
        if (en_sa_boot_i)
          start_boot = 1'b1;
      end

      WAIT_FETCH: begin
        if (fetch_en_sync[1]) begin
          start_fetch = 1'b1;
          boot_ns     = LIMBO;
        end
      end

      LIMBO: begin
        boot_ns = LIMBO;
      end
    endcase
  end

  ////////ASYNCH SIGNAL SYNCHRONIZER + EDGE DETECTOR\\\\\\\\
  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if(rst_ni == 1'b0)
    begin
      fetch_en_sync <= 2'b0;
      boot_cs       <= RESET;
    end
    else
    begin
      fetch_en_sync <= {fetch_en_sync[0],fetch_en_i};
      boot_cs       <= boot_ns;
    end
  end

  // read logic
  always_comb
  begin
    rdata_n  = '0;

    if (speriph_slave.req && speriph_slave.wen)
    begin

      case (speriph_slave.add[7:6])
      2'b00: begin
        case (speriph_slave.add[5:3])
          3'b000:
          begin
            rdata_n[0] = eoc_o;
          end

          3'b001:
          begin
            rdata_n[NB_CORES-1:0] = fetch_en_q;
          end

          3'b011:
          //      +---------------------------------------------------------+
          // ADDR |   unused   | fregfile_dis | hwpe_en | hwpe_sel | unused |
          // 0x18 |   31..13   |      12      |   11    |    10    |  9..0  |
          //      +---------------------------------------------------------+
          begin
            rdata_n[OFFSET_2+OFFSET_1+1]          = 0;
            rdata_n[OFFSET_2+OFFSET_1  ]          = 0;
            rdata_n[OFFSET_2+OFFSET_1-1:OFFSET_1] = 0;
            rdata_n[OFFSET_1-1:0]                 = 0;
            rdata_n[OFFSET_2+OFFSET_1+2]          = hwpe_sel_o;
            rdata_n[OFFSET_2+OFFSET_1+3]          = hwpe_en_o;
            rdata_n[OFFSET_2+OFFSET_1+4]          = fregfile_disable_o;
          end

          3'b100: rdata_n[0] = cluster_cg_en_o;
          3'b101: rdata_n[NB_CORES-1:0] = core_halted_i[NB_CORES-1:0];
          3'b111: rdata_n[NB_CORES-1:0] = dbg_halt_mask_q[NB_CORES-1:0];

          default:;
        endcase
      end

      2'b01:
      begin
        rdata_n = boot_addr_n[speriph_slave.add[5:2]];
      end

      2'b10, 2'b11:
      begin
          case(speriph_slave.add[3])
          1'b0:
          begin
            rdata_n[0] = TCDM_arb_policy_o[0];
          end

          1'b1:
          begin
            rdata_n[0] = TCDM_arb_policy_o[1];
          end
          endcase // speriph_slave.add[3]
      end

    endcase // speriph_slave.add[7:6]
    end
  end

  // write logic
  always_comb
  begin
    hwpe_sel_n  = hwpe_sel_o;
    hwpe_en_n   = hwpe_en_o;

    fregfile_disable_n = fregfile_disable_o;

    fetch_en_n  = fetch_en_q;
    eoc_n       = eoc_o;
    event_n     = event_o;

    boot_addr_n     = boot_addr_o;
    cluster_cg_en_n = cluster_cg_en_o;

    TCDM_arb_policy_n = TCDM_arb_policy_o;

    core_resume_o   = '0;
    dbg_halt_mask_n = dbg_halt_mask_q;

    if (speriph_slave.req && (~speriph_slave.wen))
    begin

      case (speriph_slave.add[7:6])
      2'b00:
      begin
        case (speriph_slave.add[5:3])
          3'b000: begin
            eoc_n = speriph_slave.wdata[0];
          end

          3'b001: begin
            fetch_en_n[NB_CORES-1:0] = speriph_slave.wdata[NB_CORES-1:0];
          end

          3'b010: begin
            event_n = speriph_slave.wdata[0];
          end

          3'b011: begin
            hwpe_sel_n = speriph_slave.wdata[OFFSET_2+OFFSET_1+2];
            hwpe_en_n = speriph_slave.wdata[OFFSET_2+OFFSET_1+3];
            fregfile_disable_n = speriph_slave.wdata[OFFSET_2+OFFSET_1+4];
          end
          3'b100: begin
            cluster_cg_en_n = speriph_slave.wdata[0];
          end
          3'b101: begin // Debug Status/Resume
            core_resume_o   = speriph_slave.wdata[NB_CORES-1:0];
          end
          3'b111: begin // Debug Halt Mask
            dbg_halt_mask_n = speriph_slave.wdata[NB_CORES-1:0];
          end
        endcase
      end
      2'b01:
      begin
        boot_addr_n[speriph_slave.add[5:2]] = speriph_slave.wdata;
      end

      2'b11,2'b10:
      begin
        case (speriph_slave.add[5:3])
        3'b000:  TCDM_arb_policy_n[0] = speriph_slave.wdata[0];
        3'b001:  TCDM_arb_policy_n[1] = speriph_slave.wdata[0];
        endcase
      end
    endcase // speriph_slave.add[7:6]
    end
  end


  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if(rst_ni == 1'b0)
    begin
      rdata_q           <= '0;
      id_q              <= '0;
      rvalid_q          <= 1'b0;
       
      hwpe_sel_o        <= 1'b1;
      hwpe_en_o         <= 1'b0;

      fregfile_disable_o<= 1'b0;

      fetch_en_q        <= '0;
      eoc_o             <= 1'b0;
      event_o           <= 1'b0;

      dbg_halt_mask_q   <= '0;
      core_halted_any_q <= 1'b0;

      cluster_cg_en_o   <= 1'b0;
      TCDM_arb_policy_o <= 2'b00;

      boot_addr_o       <= '{default: BOOT_ADDR};
    end
    else
    begin
      rvalid_q <= rvalid_n;

      if (rvalid_n)
      begin
        rdata_q <= rdata_n;
        id_q    <= id_n;
      end
      
      hwpe_sel_o        <= hwpe_sel_n;
      hwpe_en_o         <= hwpe_en_n;

      fregfile_disable_o<= fregfile_disable_n;

      cluster_cg_en_o   <= cluster_cg_en_n;

      eoc_o             <= eoc_n;
      event_o           <= event_n;

      dbg_halt_mask_q   <= dbg_halt_mask_n;
      core_halted_any_q <= core_halted_any_n;

      boot_addr_o       <= boot_addr_n;

      TCDM_arb_policy_o <= TCDM_arb_policy_n;

      if (start_fetch)
        fetch_en_q <= '1;
      else
        fetch_en_q <= fetch_en_n;

      if (start_boot) begin
        boot_addr_o[0] <= ROM_BOOT_ADDR;
        fetch_en_q[0]  <= 1'b1;
      end
    end
  end

  // debug halt mode handling
  assign core_halted_any_n = (|(core_halted_i & dbg_halt_mask_q)) & (~core_resume_o);
  assign core_halt_rising_edge = (~core_halted_any_q) & core_halted_any_n;

  assign core_halt_o = {NB_CORES{core_halt_rising_edge}} & dbg_halt_mask_q;

  // to check with igor
  assign speriph_slave.gnt     = 1'b1;
  assign speriph_slave.r_valid = rvalid_q;
  assign speriph_slave.r_opc   = 1'b0;
  assign speriph_slave.r_id    = id_q;
  assign speriph_slave.r_rdata = rdata_q;

  assign rvalid_n = speriph_slave.req;
  assign id_n     = speriph_slave.id;

endmodule
