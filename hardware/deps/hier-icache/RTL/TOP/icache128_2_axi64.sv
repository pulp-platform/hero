// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`define OKAY   2'b00
`define EXOKAY 2'b01
`define SLVERR 2'b10
`define DECERR 2'b11

module icache128_2_axi64
#(
    parameter ADDR_WIDTH         = 32,
    parameter DATA_WIDTH         = 128,

    parameter AXI_DATA_WIDTH     = 64,
    parameter AXI_ADDR_WIDTH     = 32,
    parameter AXI_USER_WIDTH     = 1,
    parameter AXI_ID_WIDTH       = 5,
    parameter AXI_STRB_WIDTH     = AXI_DATA_WIDTH/8
)
(
    // Clock and Reset
    input logic                           clk_i,
    input logic                           rst_ni,


    // signals from PRI cache and interconnect
    input  logic                          refill_req_i,
    output logic                          refill_gnt_o,
    input  logic  [ADDR_WIDTH-1:0]        refill_addr_i,
    output logic                          refill_r_valid_o,
    output logic  [DATA_WIDTH-1:0]        refill_r_data_o,


    // ---------------------------------------------------------
    // AXI TARG Port Declarations ------------------------------
    // ---------------------------------------------------------
    //AXI write address bus -------------- // USED// -----------
    output logic [AXI_ID_WIDTH-1:0]       aw_id_o,
    output logic [AXI_ADDR_WIDTH-1:0]     aw_addr_o,
    output logic [ 7:0]                   aw_len_o,
    output logic [ 2:0]                   aw_size_o,
    output logic [ 1:0]                   aw_burst_o,
    output logic                          aw_lock_o,
    output logic [ 3:0]                   aw_cache_o,
    output logic [ 2:0]                   aw_prot_o,
    output logic [ 3:0]                   aw_region_o,
    output logic [AXI_USER_WIDTH-1:0]     aw_user_o,
    output logic [ 3:0]                   aw_qos_o,
    output logic                          aw_valid_o,
    input  logic                          aw_ready_i,
    // ---------------------------------------------------------

    //AXI write data bus -------------- // USED// --------------
    output logic [AXI_DATA_WIDTH-1:0]     w_data_o,
    output logic [AXI_STRB_WIDTH-1:0]     w_strb_o,
    output logic                          w_last_o,
    output logic [AXI_USER_WIDTH-1:0]     w_user_o,
    output logic                          w_valid_o,
    input  logic                          w_ready_i,
    // ---------------------------------------------------------

    //AXI write response bus -------------- // USED// ----------
    input  logic   [AXI_ID_WIDTH-1:0]     b_id_i,
    input  logic   [ 1:0]                 b_resp_i,
    input  logic                          b_valid_i,
    input  logic   [AXI_USER_WIDTH-1:0]   b_user_i,
    output logic                          b_ready_o,
    // ---------------------------------------------------------

    //AXI read address bus -------------------------------------
    output logic [AXI_ID_WIDTH-1:0]       ar_id_o,
    output logic [AXI_ADDR_WIDTH-1:0]     ar_addr_o,
    output logic [ 7:0]                   ar_len_o,
    output logic [ 2:0]                   ar_size_o,
    output logic [ 1:0]                   ar_burst_o,
    output logic                          ar_lock_o,
    output logic [ 3:0]                   ar_cache_o,
    output logic [ 2:0]                   ar_prot_o,
    output logic [ 3:0]                   ar_region_o,
    output logic [AXI_USER_WIDTH-1:0]     ar_user_o,
    output logic [ 3:0]                   ar_qos_o,
    output logic                          ar_valid_o,
    input  logic                          ar_ready_i,
    // ---------------------------------------------------------

    //AXI read data bus ----------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]      r_id_i,
    input  logic [AXI_DATA_WIDTH-1:0]    r_data_i,
    input  logic [ 1:0]                  r_resp_i,
    input  logic                         r_last_i,
    input  logic [AXI_USER_WIDTH-1:0]    r_user_i,
    input  logic                         r_valid_i,
    output logic                         r_ready_o
    // ---------------------------------------------------------
);

    enum logic [2:0] { IDLE, WAIT_SAMPLE0, WAIT_SAMPLE1, DISPATCH_RDATA } CS, NS;

    logic [DATA_WIDTH/AXI_DATA_WIDTH-1:0][AXI_DATA_WIDTH-1:0] rdata_q;
    logic save_0, save_1;

    assign refill_r_data_o = rdata_q;

    assign w_data_o  = '0;
    assign w_strb_o  = '0;
    assign w_last_o  = '0;
    assign w_user_o  = '0;
    assign w_valid_o = '0;

    assign b_ready_o = 1'b0;

    assign aw_id_o      = '0;
    assign aw_addr_o    = '0;
    assign aw_len_o     = '0;
    assign aw_size_o    = '0;
    assign aw_burst_o   = '0;
    assign aw_lock_o    = '0;
    assign aw_cache_o   = '0;
    assign aw_prot_o    = '0;
    assign aw_region_o  = '0;
    assign aw_user_o    = '0;
    assign aw_qos_o     = '0;
    assign aw_valid_o   = '0;


    assign ar_id_o     = '0;
    assign ar_addr_o   = refill_addr_i;
    assign ar_size_o   = 3'b011; // 64 bit
    assign ar_len_o    =  1;     // 2 Beat transexual that you love it
    assign ar_burst_o  = '0;
    assign ar_prot_o   = '0;
    assign ar_region_o = '0;
    assign ar_lock_o   = '0;
    assign ar_cache_o  = '0;
    assign ar_qos_o    = '0;
    assign ar_user_o   = '0;



  


  // main FSM
  always_comb
  begin
    NS               = CS;

    refill_gnt_o     = 1'b0;
    refill_r_valid_o = 1'b0;

    ar_valid_o       = 1'b0;
    r_ready_o        = 1'b1;

    save_0           = 1'b0;
    save_1           = 1'b0;



    case (CS)
        // wait for a request to come in from the core
        IDLE:
        begin
            ar_valid_o = refill_req_i;

            if (refill_req_i)
            begin
                refill_gnt_o = ar_ready_i;

                if (ar_ready_i)
                begin
                    NS = WAIT_SAMPLE0;
                end
                else
                begin
                    NS = IDLE;
                end
            end
            else
            begin
                NS = IDLE;
            end
        end




      WAIT_SAMPLE0:
      begin

        save_0 = r_valid_i;

        if (r_valid_i)
        begin
            if(r_last_i)
            begin
                NS = DISPATCH_RDATA;
            end
            else
            begin
                NS = WAIT_SAMPLE1;
            end
        end
        else
        begin
           NS = WAIT_SAMPLE0; 
        end
      end

      WAIT_SAMPLE1:
      begin

        save_1 = r_valid_i;

        if (r_valid_i & r_last_i)
        begin
            NS = DISPATCH_RDATA;
        end
        else
        begin
           NS = WAIT_SAMPLE1; 
        end
      end

      DISPATCH_RDATA:
      begin
        refill_r_valid_o  = 1'b1;

        ar_valid_o = refill_req_i;

        if (refill_req_i)
        begin
            refill_gnt_o = ar_ready_i;

            if (ar_ready_i)
            begin
                NS = WAIT_SAMPLE0;
            end
            else
            begin
                NS = IDLE;
            end
        end
        else
        begin
            NS = IDLE;
        end
      end


      default:
      begin
        NS = IDLE;
      end
    endcase
  end

  // registers
  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if (~rst_ni)
    begin
      CS     <= IDLE;
      rdata_q <= '0;
    end
    else
    begin
      CS     <= NS;
      if(save_0)
        rdata_q[0] <= r_data_i;
     
     if(save_1)
        rdata_q[1] <= r_data_i;        
    end
  end






endmodule


