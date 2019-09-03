// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/*****************************************************************************
 * Company:        ERC Multitherman Lab @ DEI - University of Bologna        *
 *                 Institute of Integrated Systems @ ETH Zurich              *
 *                                                                           *
 * Engineer:       Francesco Conti - f.conti@unibo.it                        *
 *                                                                           *
 * Create Date:    26/5/2015                                                 *
 * Design Name:    perf_counters_unit                                        *
 * Module Name:    perf_counters_unit.sv                                     *
 * Project Name:   PULP                                                      *
 * Language:       SystemVerilog                                             *
 *                                                                           *
 * Description:    PULP performance counters.                                *
 *****************************************************************************/

`define PERF_HIBIT 6
`define PERF_LOBIT 3

`define PERF_CLEAR 4'h0
`define PERF_START 4'h1
`define PERF_STOP  4'h2
`define PERF_CYCLE 4'h3
`define PERF_STALL 4'h4
`define PERF_IMISS 4'h5
`define PERF_DMISS 4'h6
// `define PERF_DMA   4'h7
// `define PERF_LIC   4'h8
// `define PERF_HWCE  4'h9

module perf_counters_unit
#(
  parameter NB_CORES=4,
  parameter PER_ID_WIDTH=17
)
(
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  logic [NB_CORES-1:0][31:0]    perf_stall_cnt_i,
  input  logic [NB_CORES-1:0][31:0]    perf_cycle_cnt_i,
  input  logic [NB_CORES-1:0][31:0]    perf_imiss_cnt_i,
  input  logic [NB_CORES-1:0][31:0]    perf_dmiss_cnt_i,
  output logic                         perf_clr_o,
  output logic                         perf_en_o,
  XBAR_PERIPH_BUS.Slave perf_speriph_slave [NB_CORES-1:0] 
);

  logic [NB_CORES-1:0][31:0] r_perf_stall_cnt;
  logic [NB_CORES-1:0][31:0] r_perf_cycle_cnt;
  logic [NB_CORES-1:0][31:0] r_perf_imiss_cnt;
  logic [NB_CORES-1:0][31:0] r_perf_dmiss_cnt;
  logic                      s_perf_clr;
  logic                      s_perf_en;

  logic [NB_CORES-1:0][31:0]             s_slave_wdata;
  logic [NB_CORES-1:0][31:0]             s_slave_add;
  logic [NB_CORES-1:0]                   s_slave_req;
  logic [NB_CORES-1:0]                   s_slave_wen;
  logic [NB_CORES-1:0][PER_ID_WIDTH-1:0] s_slave_id;
  logic [NB_CORES-1:0][31:0]             s_slave_r_data;
  logic [NB_CORES-1:0]                   s_slave_r_valid;
  logic [NB_CORES-1:0][PER_ID_WIDTH-1:0] s_slave_r_id;

  logic        onecore_req;
  logic        onecore_wen;
  logic [31:0] onecore_add;

  assign perf_clr_o = s_perf_clr;
  assign perf_en_o  = s_perf_en;

  // perf counters are registered to cut long paths
  always_ff @(posedge clk_i or negedge rst_ni)
  begin : perf_counters_ff
    if(rst_ni == 1'b0) begin
      r_perf_stall_cnt <= '0;
      r_perf_cycle_cnt <= '0;
      r_perf_imiss_cnt <= '0;
      r_perf_dmiss_cnt <= '0;
    end
    else begin
      r_perf_stall_cnt <= perf_stall_cnt_i;
      r_perf_cycle_cnt <= perf_cycle_cnt_i;
      r_perf_imiss_cnt <= perf_imiss_cnt_i;
      r_perf_dmiss_cnt <= perf_dmiss_cnt_i;
    end
  end

  genvar i;
  generate

    for(i=0; i<NB_CORES; i++)
    begin : response_read_gen

      // perf_speriph_slave binding
      assign perf_speriph_slave[i].gnt     = 1'b1;
      assign perf_speriph_slave[i].r_rdata = s_slave_r_data [i]; 
      assign perf_speriph_slave[i].r_opc   = 1'b0;
      assign perf_speriph_slave[i].r_id    = s_slave_r_id   [i];
      assign perf_speriph_slave[i].r_valid = s_slave_r_valid[i];
      assign s_slave_req   [i] = perf_speriph_slave[i].req;
      assign s_slave_id    [i] = perf_speriph_slave[i].id;
      assign s_slave_wen   [i] = perf_speriph_slave[i].wen;
      assign s_slave_add   [i] = perf_speriph_slave[i].add;
      assign s_slave_wdata [i] = perf_speriph_slave[i].wdata;
    
      // response - read
      always_ff @(posedge clk_i or negedge rst_ni)
      begin : response_read_proc
        if(rst_ni == 1'b0) begin
          s_slave_r_data  [i] <= '0;
          s_slave_r_id    [i] <= '0;
          s_slave_r_valid [i] <= 1'b0;
        end
        else begin
          if((s_slave_req[i] == 1'b1) && (s_slave_wen[i] == 1'b1)) begin
            case(s_slave_add[i][`PERF_HIBIT:`PERF_LOBIT])
              `PERF_CYCLE: begin
                s_slave_r_data  [i] <= r_perf_cycle_cnt;
                s_slave_r_valid [i] <= 1'b1;
              end
              `PERF_STALL: begin
                s_slave_r_data  [i] <= r_perf_stall_cnt;
                s_slave_r_valid [i] <= 1'b1;
              end
              `PERF_IMISS: begin
                s_slave_r_data  [i] <= r_perf_imiss_cnt;
                s_slave_r_valid [i] <= 1'b1;
              end
              `PERF_DMISS: begin
                s_slave_r_data  [i] <= r_perf_dmiss_cnt;
                s_slave_r_valid [i] <= 1'b1;
              end
              default: begin
                s_slave_r_data  [i] <= 32'b0;
                s_slave_r_valid [i] <= 1'b0;
              end 
            endcase
          end
          else begin
            s_slave_r_data  [i] <= 32'b0;
            s_slave_r_valid [i] <= 1'b0;
          end
          s_slave_r_id [i] <= s_slave_id;
        end
      end

    end

  endgenerate

  always_comb
  begin : onecore_comb
    onecore_req = | s_slave_req;
    onecore_wen = & s_slave_wen;
    onecore_add = s_slave_add[0];
    for(int j=NB_CORES-1; j>=0; j--) begin
      if((s_slave_req[j] == 1'b1) && (s_slave_wen[j] == 1'b0))
        onecore_add = s_slave_add[j];
    end
  end 

  // response - write
  always_ff @(posedge clk_i or negedge rst_ni)
  begin : response_write_proc
    if(rst_ni == 1'b0) begin
      s_perf_en  <= 1'b0;
      s_perf_clr <= 1'b1;
    end
    else begin
      if((onecore_req == 1'b1) && (onecore_wen == 1'b0)) begin
        case(onecore_add[`PERF_HIBIT:`PERF_LOBIT])
          `PERF_CLEAR: begin
            s_perf_en  <= s_perf_en;
            s_perf_clr <= 1'b1;
          end
          `PERF_START: begin
            s_perf_en  <= 1'b1;
            s_perf_clr <= 1'b0;
          end
          `PERF_STOP: begin
            s_perf_en  <= 1'b0;
            s_perf_clr <= 1'b0;
          end
          default: begin
            s_perf_en  <= s_perf_en;
            s_perf_clr <= 1'b0;
          end 
        endcase
      end
      else begin
        s_perf_en  <= s_perf_en;
        s_perf_clr <= 1'b0;
      end
    end
  end

endmodule

