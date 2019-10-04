// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Davide Rossi <davide.rossi@unibo.it>

module per2axi_res_channel
#(
   // PARAMETERS
   parameter NB_CORES       = 4,
   parameter PER_ADDR_WIDTH = 32,
   parameter PER_ID_WIDTH   = 5,
   parameter AXI_ADDR_WIDTH = 32,
   parameter AXI_DATA_WIDTH = 64,
   parameter AXI_USER_WIDTH = 6,
   parameter AXI_ID_WIDTH   = 3
)
(
   input  logic                      clk_i,
   input  logic                      rst_ni,

   // PERIPHERAL INTERCONNECT SLAVE
   //***************************************
   //RESPONSE CHANNEL
   output logic                      per_slave_r_valid_o,
   output logic                      per_slave_r_opc_o,
   output logic [PER_ID_WIDTH-1:0]   per_slave_r_id_o,
   output logic [31:0]               per_slave_r_rdata_o,

   // TRYX CTRL
   output logic [NB_CORES-1:0]       axi_xresp_decerr_o,
   output logic [NB_CORES-1:0]       axi_xresp_slverr_o,
   output logic [NB_CORES-1:0]       axi_xresp_valid_o,

   // AXI4 MASTER
   //***************************************
   // READ DATA CHANNEL
   input  logic                      axi_master_r_valid_i,
   input  logic [AXI_DATA_WIDTH-1:0] axi_master_r_data_i,
   input  logic [1:0]                axi_master_r_resp_i,
   input  logic                      axi_master_r_last_i,
   input  logic [AXI_ID_WIDTH-1:0]   axi_master_r_id_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_master_r_user_i,
   output logic                      axi_master_r_ready_o,

   // WRITE RESPONSE CHANNEL
   input  logic                      axi_master_b_valid_i,
   input  logic [1:0]                axi_master_b_resp_i,
   input  logic [AXI_ID_WIDTH-1:0]   axi_master_b_id_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_master_b_user_i,
   output logic                      axi_master_b_ready_o,

   // CONTROL SIGNALS
   input logic                       atop_req_i,
   input logic [AXI_ID_WIDTH-1:0]    atop_id_i,
   input logic [AXI_ADDR_WIDTH-1:0]  atop_add_i,
   
   input logic                       trans_req_i,
   input logic [AXI_ID_WIDTH-1:0]    trans_id_i,
   input logic [AXI_ADDR_WIDTH-1:0]  trans_add_i
);

   logic [31:0]                       s_per_slave_r_data;
   logic [PER_ID_WIDTH-1:0]           s_read_add_buf;

   typedef enum logic [1:0] { NONE, REQUEST, WAIT_R, WAIT_B } atop_res_t;
   atop_res_t [PER_ID_WIDTH-1:0] atop_state_d, atop_state_q;
   
   // Handle responses.
   always_comb begin
      axi_master_b_ready_o = 1'b0;
      axi_master_r_ready_o = 1'b0;
      axi_xresp_decerr_o   = '0;
      axi_xresp_slverr_o   = '0;
      axi_xresp_valid_o    = '0;
      per_slave_r_id_o     = '0;
      per_slave_r_opc_o    = '0;
      per_slave_r_rdata_o  = '0;
      per_slave_r_valid_o  = 1'b0;

      if (axi_master_r_valid_i) begin
         axi_master_r_ready_o = 1'b1;
         per_slave_r_id_o[axi_master_r_id_i] = 1'b1;
         per_slave_r_rdata_o = s_per_slave_r_data;
         per_slave_r_valid_o = 1'b1;
         if (axi_master_r_resp_i[1]) begin // error
            axi_xresp_valid_o[axi_master_r_id_i] = 1'b1;
            if (axi_master_r_resp_i[0]) begin // decoding error
               axi_xresp_decerr_o[axi_master_r_id_i] = 1'b1;
            end else begin // slave error (e.g. RAB miss)
               axi_xresp_slverr_o[axi_master_r_id_i] = 1'b1;
            end
         end
      end else if (axi_master_b_valid_i) begin
         axi_master_b_ready_o = 1'b1;
         if (atop_state_q[axi_master_b_id_i] == NONE) begin
            per_slave_r_valid_o = 1'b1;
            per_slave_r_id_o[axi_master_b_id_i] = 1'b1;

            // Forward response/error to core.
            // axi_master_b_resp_i[1:0] -> per_slave_r_rdata_o[1:0]
            // 00 -> 01, 01 -> 00, 10 -> 10, 11 -> 11
            per_slave_r_rdata_o
               = {30'b0, axi_master_b_resp_i[1], axi_master_b_resp_i[1] ~^ axi_master_b_resp_i[0]};
            if (axi_master_b_resp_i[1]) begin // error
               axi_xresp_valid_o [axi_master_b_id_i] = 1'b1;
               if (axi_master_b_resp_i[0]) begin // decording error
                  axi_xresp_decerr_o[axi_master_b_id_i] = 1'b1;
               end else begin // slave error (e.g. RAB miss)
                  axi_xresp_slverr_o[axi_master_b_id_i] = 1'b1;
               end
            end
         end
      end
   end

   // Atomic memory operations
   
   generate
      for (genvar i = 0; i < PER_ID_WIDTH; i++) begin
         always_comb begin
            atop_state_d[i] = atop_state_q[i];

            unique case (atop_state_q[i])
               NONE: begin
                  if (atop_req_i && (atop_id_i == i)) begin
                     atop_state_d[i] = REQUEST;
                  end
               end

               REQUEST: begin
                  if (axi_master_r_valid_i && axi_master_r_ready_o && (axi_master_r_id_i == i)) begin
                     atop_state_d[i] = WAIT_B;
                  end
                  if (axi_master_b_valid_i && axi_master_b_ready_o && (axi_master_b_id_i == i)) begin
                     atop_state_d[i] = WAIT_R;
                  end
                  if (axi_master_r_valid_i && axi_master_r_ready_o && (axi_master_r_id_i == i) &&
                      axi_master_b_valid_i && axi_master_b_ready_o && (axi_master_b_id_i == i)) begin
                     atop_state_d[i] = NONE;
                  end
               end

               WAIT_R: begin
                  if (axi_master_r_valid_i && axi_master_r_ready_o && (axi_master_r_id_i == i)) begin
                     atop_state_d[i] = NONE;
                  end
               end

               WAIT_B: begin
                  if (axi_master_b_valid_i && axi_master_b_ready_o && (axi_master_b_id_i == i)) begin
                     atop_state_d[i] = NONE;
                  end
               end
            
               default : /* default */;
            endcase


         end

         always_ff @(posedge clk_i or negedge rst_ni) begin
            if(~rst_ni) begin
               atop_state_q[i] <= NONE;
            end else begin
               atop_state_q[i] <= atop_state_d[i];
            end
         end

      end
   endgenerate

   
   // STORES REQUEST ADDRESS BIT 2 ONLY IF A READ OPERATION OCCURS
   always_ff @ (posedge clk_i, negedge rst_ni)
   begin
      if(rst_ni == 1'b0)
      begin
         s_read_add_buf <= '0;
      end
      else
      begin
          if(trans_req_i == 1'b1)
          begin
             s_read_add_buf[trans_id_i] <= trans_add_i[2];
          end
          if(atop_req_i == 1'b1)
          begin
             s_read_add_buf[atop_id_i] <= atop_add_i[2];
          end
      end
   end
   
   // FORWARD 32-bit AXI MSBs or LSBs TO THE PERIPHERAL INTERCONNECT DEPENDING ON THE REQUEST ADDRESS
   always_comb
   begin
        if ( s_read_add_buf[axi_master_r_id_i] == 1'b0 )
        begin
             s_per_slave_r_data = axi_master_r_data_i[31:0];
        end
        else
        begin
             s_per_slave_r_data = axi_master_r_data_i[63:32];
        end
   end
   
endmodule
