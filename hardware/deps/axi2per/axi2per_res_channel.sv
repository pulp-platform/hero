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

module axi2per_res_channel
#(
   // PARAMETERS
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

   // PERIPHERAL INTERCONNECT MASTER
   //***************************************
   //RESPONSE CHANNEL
   input logic                       per_master_r_valid_i,
   input logic                       per_master_r_opc_i,
   input logic [31:0]                per_master_r_rdata_i,

   // AXI4 MASTER
   //***************************************
   // READ DATA CHANNEL
   output logic                      axi_slave_r_valid_o,
   output logic [AXI_DATA_WIDTH-1:0] axi_slave_r_data_o,
   output logic [1:0]                axi_slave_r_resp_o,
   output logic                      axi_slave_r_last_o,
   output logic [AXI_ID_WIDTH-1:0]   axi_slave_r_id_o,
   output logic [AXI_USER_WIDTH-1:0] axi_slave_r_user_o,
   input  logic                      axi_slave_r_ready_i,

   // WRITE RESPONSE CHANNEL
   output logic                      axi_slave_b_valid_o,
   output logic [1:0]                axi_slave_b_resp_o,
   output logic [AXI_ID_WIDTH-1:0]   axi_slave_b_id_o,
   output logic [AXI_USER_WIDTH-1:0] axi_slave_b_user_o,
   input  logic                      axi_slave_b_ready_i,

   // CONTROL SIGNALS
   input logic                       trans_req_i,
   input logic                       trans_we_i,
   input logic [AXI_ID_WIDTH-1:0]    trans_id_i,
   input logic [AXI_ADDR_WIDTH-1:0]  trans_add_i,
   output logic                      trans_r_valid_o
);
   
   logic [AXI_DATA_WIDTH-1:0]         s_axi_slave_r_data;
   
   logic [31:0]                       s_per_master_r_data;
   
   logic                              s_trans_we_buf;
   logic [AXI_ID_WIDTH-1:0]           s_trans_id_buf;
   logic                              s_trans_add_alignment;  //0 --> aligned to 64bit, 1--> not aligned to 64bit
   
   enum logic  { TRANS_IDLE, TRANS_PENDING } CS, NS;
   
   // UPDATE THE STATE
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          begin
             CS <= TRANS_IDLE;
          end
        else
          begin
             CS <= NS;
          end
     end
   
   // COMPUTE NEXT STATE
   always_comb
     begin
        
        axi_slave_r_valid_o = '0;
        axi_slave_r_data_o  = '0;
        axi_slave_r_last_o  = '0;
        axi_slave_r_id_o    = '0;
        
        axi_slave_b_valid_o = '0;
        axi_slave_b_id_o    = '0;
        
        trans_r_valid_o     = '0;
        
        NS                  = TRANS_IDLE;
        
        case(CS)
          
          TRANS_IDLE:
            if ( per_master_r_valid_i == 1'b1 ) // RESPONSE VALID FROM PERIPHERAL INTERCONNECT
              begin
                 if ( ( s_trans_we_buf == 1'b1 &&  // READ OPERATION
                        axi_slave_r_ready_i == 1'b1 ) ||  // THE AXI READ BUFFER IS ABLE TO ACCEPT A TRANSACTION
                      ( s_trans_we_buf == 1'b0 &&
                        axi_slave_b_ready_i == 1'b1 ) )  // THE AXI WRITE RESPONSE BUFFER IS ABLE TO ACCEPT A TRANSACTION
                   begin
                      NS = TRANS_PENDING;
                   end
              end
          
          TRANS_PENDING:
            if ( s_trans_we_buf == 1'b1 &&  // READ OPERATION
                 axi_slave_r_ready_i == 1'b1 )  // THE AXI READ BUFFER IS ABLE TO ACCEPT A TRANSACTION
              begin
                 axi_slave_r_valid_o = 1'b1;
                 axi_slave_r_last_o  = 1'b1;
                 axi_slave_r_data_o  = s_axi_slave_r_data;
                 axi_slave_r_id_o    = s_trans_id_buf;
                 
                 trans_r_valid_o     = 1'b1;
                 
                 NS = TRANS_IDLE;
              end
            else
              if ( trans_we_i == 1'b0 &&
                   axi_slave_b_ready_i == 1'b1 ) // THE AXI WRITE RESPONSE BUFFER IS ABLE TO ACCEPT A TRANSACTION
                begin
                   axi_slave_b_valid_o = 1'b1;
                   axi_slave_b_id_o    = s_trans_id_buf;
                   
                   trans_r_valid_o     = 1'b1;
                   
                   NS = TRANS_IDLE;
                end
              else
                begin
                   NS = TRANS_PENDING;
                end
        endcase
     end
   
   // STORES REQUEST ADDRESS BIT 2 TRANSFER TYPE AND THE ID WHEN A REQUEST OCCURS ON THE REQ CHANNEL
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             s_trans_we_buf        <= '0;
             s_trans_add_alignment <= 1'b0;
             s_trans_id_buf        <= '0;
          end
        else
          begin
             if(trans_req_i == 1'b1)
               begin
                  s_trans_we_buf        <= trans_we_i;
                  s_trans_add_alignment <= trans_add_i[2];
                  s_trans_id_buf        <= trans_id_i;
               end
          end
     end
   
   // STORES RDATA WHEN RVALID SIGNAL IS ASSERTED
   always_ff @ (posedge clk_i, negedge rst_ni)
     if (rst_ni == 1'b0)
       begin
          s_per_master_r_data <= '0;
       end
     else
       begin
          if(per_master_r_valid_i == 1'b1)
            begin
               s_per_master_r_data <= per_master_r_rdata_i;
            end
       end
   
   // SELECT MSB OR LSBS OF DATA
   always_comb
     begin
        if ( s_trans_add_alignment == 1'b0 )
          begin
             s_axi_slave_r_data = {32'b0,s_per_master_r_data};
          end
        else
          begin
             s_axi_slave_r_data = {s_per_master_r_data,32'b0};
          end
     end
   
   // UNUSED SIGNALS
   assign axi_slave_r_resp_o = '0;
   assign axi_slave_r_user_o = '0;
   assign axi_slave_b_resp_o = '0;
   assign axi_slave_b_user_o = '0;
   
endmodule
