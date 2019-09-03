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

module axi2per_req_channel
#(
   // PARAMETERS
   parameter PER_ADDR_WIDTH = 32,
   parameter PER_ID_WIDTH   = 5,
   parameter AXI_ADDR_WIDTH = 32,
   parameter AXI_DATA_WIDTH = 64,
   parameter AXI_USER_WIDTH = 6,
   parameter AXI_ID_WIDTH   = 3,
   // LOCAL PARAMETERS --> DO NOT OVERRIDE
   parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH/8 // DO NOT OVERRIDE
)
(
   input logic                       clk_i,
   input logic                       rst_ni,

   input  logic [5:0]                cluster_id_i,

   input  logic                      axi_slave_aw_valid_i,
   input  logic [AXI_ADDR_WIDTH-1:0] axi_slave_aw_addr_i,
   input  logic [2:0]                axi_slave_aw_prot_i,
   input  logic [3:0]                axi_slave_aw_region_i,
   input  logic [7:0]                axi_slave_aw_len_i,
   input  logic [2:0]                axi_slave_aw_size_i,
   input  logic [1:0]                axi_slave_aw_burst_i,
   input  logic                      axi_slave_aw_lock_i,
   input  logic [5:0]                axi_slave_aw_atop_i,
   input  logic [3:0]                axi_slave_aw_cache_i,
   input  logic [3:0]                axi_slave_aw_qos_i,
   input  logic [AXI_ID_WIDTH-1:0]   axi_slave_aw_id_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_slave_aw_user_i,
   output logic                      axi_slave_aw_ready_o,

   // READ ADDRESS CHANNEL
   input  logic                      axi_slave_ar_valid_i,
   input  logic [AXI_ADDR_WIDTH-1:0] axi_slave_ar_addr_i,
   input  logic [2:0]                axi_slave_ar_prot_i,
   input  logic [3:0]                axi_slave_ar_region_i,
   input  logic [7:0]                axi_slave_ar_len_i,
   input  logic [2:0]                axi_slave_ar_size_i,
   input  logic [1:0]                axi_slave_ar_burst_i,
   input  logic                      axi_slave_ar_lock_i,
   input  logic [3:0]                axi_slave_ar_cache_i,
   input  logic [3:0]                axi_slave_ar_qos_i,
   input  logic [AXI_ID_WIDTH-1:0]   axi_slave_ar_id_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_slave_ar_user_i,
   output logic                      axi_slave_ar_ready_o,

   // WRITE DATA CHANNEL
   input  logic                      axi_slave_w_valid_i,
   input  logic [AXI_DATA_WIDTH-1:0] axi_slave_w_data_i,
   input  logic [AXI_STRB_WIDTH-1:0] axi_slave_w_strb_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_slave_w_user_i,
   input  logic                      axi_slave_w_last_i,
   output logic                      axi_slave_w_ready_o,

   // PERIPHERAL REQUEST CHANNEL
   output logic                      per_master_req_o,
   output logic [PER_ADDR_WIDTH-1:0] per_master_add_o,
   output logic                      per_master_we_o,
   output logic [31:0]               per_master_wdata_o,
   output logic [3:0]                per_master_be_o,
   input  logic                      per_master_gnt_i,

   // CONTROL SIGNALS
   output logic                      trans_req_o,
   output logic                      trans_we_o,
   output logic [AXI_ID_WIDTH-1:0]   trans_id_o,
   output logic [AXI_ADDR_WIDTH-1:0] trans_add_o, 
   input  logic                      trans_r_valid_i,

   // BUSY SIGNAL
   output logic                      busy_o
);
   
   enum logic { TRANS_IDLE, TRANS_PENDING } CS, NS;
   
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
        
        axi_slave_aw_ready_o = '0;
        axi_slave_ar_ready_o = '0;
        axi_slave_w_ready_o  = '0;
        
        per_master_req_o     = '0;
        per_master_add_o     = '0;
        per_master_we_o      = '0;
        per_master_wdata_o   = '0;
        per_master_be_o      = '0;
        
        trans_req_o          = '0;
        trans_we_o           = '0;
        trans_id_o           = '0;
        trans_add_o          = '0;
        
        busy_o               = '0;
        
        NS                   = TRANS_IDLE;
        
        case(CS)
          
          TRANS_IDLE:
            
            begin
               if ( axi_slave_ar_valid_i == 1'b1 ) // REQUEST FROM READ ADDRESS CHANNEL
                 begin
                    per_master_req_o = 1'b1;                     // MAKE THE REQUEST TO THE PHERIPHERAL INTERCONNECT
                    per_master_we_o  = 1'b1;                     // READ OPERATION
                    per_master_add_o = axi_slave_ar_addr_i;      // ADDRESS COMES FROM ADDRESS READ CHANNEL
                    
                    if ( per_master_gnt_i == 1'b1 ) // THE REQUEST IS ACKNOWLEDGED FROM THE PERIPHERAL INTERCONNECT
                      begin
                         axi_slave_ar_ready_o = 1'b1; // POP DATA FROM THE ADDRESS READ BUFFER
                         
                         trans_req_o          = 1'b1;                // NOTIFY THE RESPONSE CHANNEL THAT THERE IS A PENDING REQUEST
                         trans_we_o           = 1'b1;                // NOTIFY THE RESPONSE CHANNEL THE TYPE OF THE PENDING REQUEST
                         trans_id_o           = axi_slave_ar_id_i;   // NOTIFY THE RESPONSE CHANNEL THE ID OF THE PENDING REQUEST
                         trans_add_o          = axi_slave_ar_addr_i; // NOTIFY THE RESPONSE CHANNEL THE ADDRESS OF THE PENDING REQUEST
                         
                         NS                   = TRANS_PENDING;
                      end
                 end
               else
                 begin
                    if ( axi_slave_aw_valid_i == 1'b1 && // REQUEST FROM WRITE ADDRESS CHANNEL
                         axi_slave_w_valid_i == 1'b1 )   // REQUEST FROM WRITE DATA CHANNEL
                      begin
                         per_master_req_o = 1'b1;                     // MAKE THE REQUEST TO THE PHERIPHERAL INTERCONNECT
                         per_master_we_o  = 1'b0;                     // WRITE OPERATION
                         per_master_add_o = axi_slave_aw_addr_i;      // ADDRESS COMES FROM WRITE ADDRESS CHANNEL
                         
                         if ( axi_slave_aw_addr_i[2] == 1'b0 ) // FORWARD THE RIGHT AXI DATA TO THE PERIPHERAL BYTE ENABLE
                           begin
                              per_master_wdata_o  = axi_slave_w_data_i[31:0];
                           end
                         else
                           begin
                              per_master_wdata_o  = axi_slave_w_data_i[63:32];
                           end
                         
                         if ( axi_slave_aw_addr_i[2] == 1'b0 ) // FORWARD THE RIGHT AXI STROBE TO THE PERIPHERAL BYTE ENABLE
                           begin
                              per_master_be_o  = axi_slave_w_strb_i[3:0];
                           end
                         else
                           begin
                              per_master_be_o  = axi_slave_w_strb_i[7:4];
                           end
                         
                         if ( per_master_gnt_i == 1'b1 ) // THE REQUEST IS ACKNOWLEDGED FROM THE PERIPHERAL INTERCONNECT
                           begin
                              axi_slave_aw_ready_o = 1'b1; // POP DATA FROM THE WRITE ADDRESS BUFFER
                              axi_slave_w_ready_o  = 1'b1; // POP DATA FROM THE WRITE DATA BUFFER
                              
                              trans_req_o          = 1'b1;                // NOTIFY THE RESPONSE CHANNEL THAT THERE IS A PENDING REQUEST
                              trans_we_o           = 1'b0;                // NOTIFY THE RESPONSE CHANNEL THE TYPE OF THE PENDING REQUEST
                              trans_id_o           = axi_slave_aw_id_i;   // NOTIFY THE RESPONSE CHANNEL THE ID OF THE PENDING REQUEST
                              trans_add_o          = axi_slave_aw_addr_i; // NOTIFY THE RESPONSE CHANNEL THE ADDRESS OF THE PENDING REQUEST
                              
                              NS                   = TRANS_PENDING;
                           end
                      end
                 end
                 per_master_add_o = per_master_add_o - (32'h0040_0000 * cluster_id_i);
            end
          
          TRANS_PENDING:
            
            begin
               axi_slave_aw_ready_o = '0;     // PENDING TRANSACTION WRITE ADDRESS CHANNEL NOT READY
               axi_slave_ar_ready_o = '0;     // PENDING TRANSACTION READ ADDRESS CHANNEL NOT READY
               axi_slave_w_ready_o  = '0;     // PENDING TRANSACTION WRITE DATA CHANNEL NOT READY
               
               busy_o               = '1;
               
               if ( trans_r_valid_i == 1'b1 ) // RECEIVED NOTIFICATION FROM RESPONSE CHANNEL: TRANSACTION COMPLETED
                 begin
                    NS = TRANS_IDLE;
                 end
               else
                 begin
                    NS = TRANS_PENDING;
                 end
            end
        endcase
     end
   
   // UNUSED SIGNALS
   //axi_slave_aw_prot_i
   //axi_slave_aw_region_i
   //axi_slave_aw_len_i
   //axi_slave_aw_lock_i
   //axi_slave_aw_atop_i
   //axi_slave_aw_cache_i
   //axi_slave_aw_qos_i
   //axi_slave_aw_user_i
   
   //axi_slave_ar_prot_i
   //axi_slave_ar_region_i
   //axi_slave_ar_len_i
   //axi_slave_ar_lock_i
   //axi_slave_ar_cache_i
   //axi_slave_ar_qos_i
   //axi_slave_ar_user_i
   
   //axi_slave_w_user_i
   
endmodule
