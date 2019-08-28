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

module axi2mem_rd_channel
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
   input  logic                           clk_i,
   input  logic                           rst_ni,
   input  logic                           test_en_i,

   // AXI4 MASTER
   //***************************************
   // READ ADDRESS CHANNEL
   input  logic                           axi_slave_ar_valid_i,
   input  logic [AXI_ADDR_WIDTH-1:0]      axi_slave_ar_addr_i,
   input  logic [2:0]                     axi_slave_ar_prot_i,
   input  logic [3:0]                     axi_slave_ar_region_i,
   input  logic [7:0]                     axi_slave_ar_len_i,
   input  logic [2:0]                     axi_slave_ar_size_i,
   input  logic [1:0]                     axi_slave_ar_burst_i,
   input  logic                           axi_slave_ar_lock_i,
   input  logic [3:0]                     axi_slave_ar_cache_i,
   input  logic [3:0]                     axi_slave_ar_qos_i,
   input  logic [AXI_ID_WIDTH-1:0]        axi_slave_ar_id_i,
   input  logic [AXI_USER_WIDTH-1:0]      axi_slave_ar_user_i,
   output logic                           axi_slave_ar_ready_o,

   // READ DATA CHANNEL
   output logic                           axi_slave_r_valid_o,
   output logic [AXI_DATA_WIDTH-1:0]      axi_slave_r_data_o,
   output logic [1:0]                     axi_slave_r_resp_o,
   output logic                           axi_slave_r_last_o,
   output logic [AXI_ID_WIDTH-1:0]        axi_slave_r_id_o,
   output logic [AXI_USER_WIDTH-1:0]      axi_slave_r_user_o,
   input  logic                           axi_slave_r_ready_i,

   // CONTROL SIGNALS
   output logic [1:0][5:0]                trans_id_o,
   output logic [1:0][31:0]               trans_add_o,
   output logic [1:0][3:0]                trans_be_o,  //Byte enable is used for test and set, to avoid curruption of neighboor locations
   output logic [1:0]                     trans_req_o,
   output logic [1:0]                     trans_last_o,
   input  logic [1:0]                     trans_gnt_i,

   // Data Signals
   input  logic [63:0]                    data_dat_i,
   input  logic [5:0]                     data_id_i,
   input  logic                           data_last_i,
   output logic                           data_req_o,
   input  logic                           data_gnt_i
);
   
   enum logic  { TRANS_IDLE, TRANS_RUN } CS, NS;
   
   logic [7:0]                             s_axi_slave_ar_len;
   logic [AXI_ADDR_WIDTH-1:0]              s_axi_slave_ar_addr;
   logic [AXI_ID_WIDTH-1:0]                s_axi_slave_ar_id;
   
   logic                                   s_start_count;
   logic [12:0]                            s_trans_count;
   logic [31:0]                            s_trans_addr;
   logic                                   s_trans_complete;
   
   logic                                   s_ready_id;
   
   //**********************************************************
   //********************* REQUEST CHANNEL ********************
   //**********************************************************
   
   //SAMPLES THE NUMBER OF TRANSACTIONS AND THE ADDRESS
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             s_axi_slave_ar_len  <= '0;
             s_axi_slave_ar_addr <= '0;
          end
        else
          begin
             if ( axi_slave_ar_valid_i == 1'b1 && axi_slave_ar_ready_o == 1'b1 )
               begin
                  s_axi_slave_ar_len  <= axi_slave_ar_len_i;
                  s_axi_slave_ar_addr <= {axi_slave_ar_addr_i[AXI_ADDR_WIDTH-1:3],3'b000};
               end
          end
     end
   
   //COUNTER FOR NUMBER OF CELLS
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          s_trans_count <= '0;
        else
          if ( trans_req_o == 2'b11 && trans_gnt_i == 2'b11 && s_start_count == 1'b1 )
            s_trans_count <= '0;
          else
            if ( trans_req_o == 2'b11 && trans_gnt_i == 2'b11 )
              s_trans_count <= s_trans_count+1;
            else
              s_trans_count <= s_trans_count;
     end
   
   always_comb
     begin
        if ( s_trans_count ==  s_axi_slave_ar_len-1 )
          s_trans_complete = 1'b1;
        else
          s_trans_complete = 1'b0;
     end
   
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
        
        axi_slave_ar_ready_o = '0;
        
        trans_add_o          = '0;
        trans_req_o          = '0;
        trans_last_o         = '0;
        
        s_start_count        = '0;

        if(axi_slave_ar_size_i == 3'b010) // 32 bit transactions
        begin : _32_BIT_TRANS_
          trans_be_o = ( axi_slave_ar_addr_i[2] ) ? 8'hF0 : 8'h0F ;
        end 
        else
        begin : _64_BIT_TRANS_
          trans_be_o = '1;
        end


        
        NS               = TRANS_IDLE;
        
        case(CS)
          
          TRANS_IDLE:
            
            begin
               if ( axi_slave_ar_valid_i == 1'b1 &&                      // REQUEST FROM READ ADDRESS CHANNEL
                    trans_gnt_i[0] == 1'b1 &&  trans_gnt_i[1] == 1'b1 && // TCDM CMD QUEUE IS AVAILABLE
                    s_ready_id == 1'b1 )                                 
                 begin
                    
                    axi_slave_ar_ready_o = 1'b1;
                    
                    trans_req_o[0] = 1'b1;
                    trans_req_o[1] = 1'b1;
                    
                    trans_add_o[0] = {axi_slave_ar_addr_i[AXI_ADDR_WIDTH-1:3],3'b000};
                    trans_add_o[1] = {axi_slave_ar_addr_i[AXI_ADDR_WIDTH-1:3],3'b000} + 4;
                    
                    if ( axi_slave_ar_len_i == 1'b0 ) // SINGLE BEAT TRANSACTION
                      begin
                         trans_last_o[0] = 1'b1;
                         trans_last_o[1] = 1'b1;
                         
                         NS = TRANS_IDLE;
                      end
                    else // BURST
                      begin
                         s_start_count = 1'b1;
                         
                         NS = TRANS_RUN;
                      end
                 end
               else
                 begin
                    NS = TRANS_IDLE;
                 end
            end
          
          TRANS_RUN:
            begin
               axi_slave_ar_ready_o = 1'b0;
               
               if ( trans_gnt_i[0] == 1'b1 && trans_gnt_i[1] == 1'b1 )
                 begin
                    
                    trans_req_o[0]       = 1'b1;
                    trans_req_o[1]       = 1'b1;
                    
                    trans_add_o[0]       = s_trans_addr;
                    trans_add_o[1]       = s_trans_addr + 4;
                    
                    if ( s_trans_complete == 1'b1 )
                      begin
                         trans_last_o[0] = 1'b1;
                         trans_last_o[1] = 1'b1;
                         
                         NS          = TRANS_IDLE;
                      end
                    else
                      begin
                         NS = TRANS_RUN;
                      end
                 end
               else
                 begin
                    NS = TRANS_RUN;
                 end
            end
          
          default:
            begin
            end
          
        endcase
     end
   
   assign s_trans_addr  = s_axi_slave_ar_addr + ( s_trans_count + 1 << 3 );
   
   assign trans_id_o[0] = axi_slave_ar_id_i;
   assign trans_id_o[1] = axi_slave_ar_id_i;
   
   //**********************************************************
   //**************** RESPONSE CHANNEL ************************
   //**********************************************************
   
   always_comb
     begin
        
        data_req_o          = 1'b0;
        axi_slave_r_valid_o = 1'b0;
        axi_slave_r_last_o  = 1'b0;
        
        if ( data_gnt_i == 1'b1 &&          // DATA IS AVAILABLE ON THE DATA FIFO
             axi_slave_r_ready_i == 1'b1 )  // THE AXI INTERFACE IS ABLE TO ACCETT A DATA
          
          begin
             if ( data_last_i == 1'b1 ) // LAST BEAT
               begin
                  data_req_o          = 1'b1;
                  axi_slave_r_valid_o = 1'b1;
                  axi_slave_r_last_o  = 1'b1;
               end
             else
               begin
                  data_req_o          = 1'b1;
                  axi_slave_r_valid_o = 1'b1;
                  axi_slave_r_last_o  = 1'b0;
               end
          end
        else
          begin
             data_req_o          = 1'b0;
             axi_slave_r_valid_o = 1'b0;
             axi_slave_r_last_o  = 1'b0;
          end
     end
   
   //**********************************************************
   //**************** FIFO TO STORE R_ID **********************
   //**********************************************************
   
   generic_fifo
   #(
      .DATA_WIDTH   ( AXI_ID_WIDTH ),
      .DATA_DEPTH   ( 4            )
   )
   r_id_buf_i
   (
      .clk          ( clk_i                                                         ),
      .rst_n        ( rst_ni                                                        ),
      .test_mode_i  ( test_en_i                                                     ),

      .valid_o      (                                                               ),
      .data_o       ( s_axi_slave_ar_id                                             ),
      .grant_i      ( axi_slave_r_last_o                                            ),

      .valid_i      ( axi_slave_ar_valid_i == 1'b1 && axi_slave_ar_ready_o == 1'b1  ),
      .data_i       ( axi_slave_ar_id_i                                             ),
      .grant_o      ( s_ready_id                                                    )
   );
   
   assign axi_slave_r_data_o  = data_dat_i;
   assign axi_slave_r_resp_o  = '0;
   assign axi_slave_r_id_o    = s_axi_slave_ar_id;
   assign axi_slave_r_user_o  = '0;
   
endmodule
