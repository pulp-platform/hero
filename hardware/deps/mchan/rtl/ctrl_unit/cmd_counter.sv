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

module cmd_counter
  #(
    parameter MCHAN_LEN_WIDTH    = 16,
    parameter TWD_COUNT_WIDTH    = 16,
    parameter TWD_STRIDE_WIDTH   = 16,
    parameter EXT_ADD_WIDTH      = 29,
    parameter MCHAN_BURST_LENGTH = 64
    )
   (
    
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    input  logic                        cmd_req_i,
    input  logic [MCHAN_LEN_WIDTH-1:0]  cmd_len_i,
    input  logic                        cmd_twd_i,
    input  logic [TWD_COUNT_WIDTH-1:0]  cmd_count_i,
    input  logic [TWD_STRIDE_WIDTH-1:0] cmd_stride_i,
    
    input  logic [EXT_ADD_WIDTH-1:0]    ext_add_i,
    
    output logic                        cmd_req_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  cmd_nb_o
    
    );
   
   // FSM STATES SIGNALS
   enum                                 `ifdef SYNTHESIS logic [1:0] `endif { TRANS_IDLE, TRANS_RUN } CS, NS;
   
   logic [MCHAN_LEN_WIDTH-1:0]          s_mchan_rem_len, s_mchan_cur_len, s_mchan_first_len, s_mchan_init_rem_len, s_mchan_init_rem_len_plus;
   logic                                s_trans_complete,s_ext_add_burst_crossed,s_ext_add_burst_aligned;
   
   logic [TWD_COUNT_WIDTH-1:0]          s_cmd_count;
   logic [TWD_STRIDE_WIDTH-1:0]         s_cmd_stride;
   logic                                s_cmd_twd;
   logic [EXT_ADD_WIDTH-1:0]            s_mchan_ext_add;
   
   //**********************************************************
   //***** SAMPLES THE OPCODE, SID OF CURRENT TRANSFER ********
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             s_cmd_count  <= 0;
             s_cmd_stride <= 0;
             s_cmd_twd    <= 0;
          end
        else
          begin
             if ( cmd_req_i == 1'b1 ) // SAMPLES DATA AT THE BEGINNING OF EACH TRANSFER
               begin
                  s_cmd_count  <= cmd_count_i;
                  s_cmd_stride <= cmd_stride_i;
                  s_cmd_twd    <= cmd_twd_i;
               end
          end
     end
   
   //**********************************************************
   //***** COMPUTES THE LENGTH OF CURRNT TRANSACTION **********
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             s_mchan_cur_len <= '0;  // LENGTH OF CURRENT CMD TRANSACTION
             s_mchan_rem_len <= '0;  // REMAINING LENGHT OF CURRENT CMD TRANSFER
          end
        else
          begin
             if ( cmd_req_i == 1 || cmd_req_o == 1 ) // ACTIVATION FUNCTION FOR AUTOMATIC CLOCK GATING
               begin
                  if ( cmd_req_i == 1 ) // SAMPLES DATA AT THE BEGINNING OF EACH CMD TRANSFER
                    begin
                       if ( ( cmd_len_i <= cmd_count_i ) || ( cmd_twd_i == 0 ) )
                         begin
                            s_mchan_cur_len <= cmd_len_i;
                            s_mchan_rem_len <= 0;
                         end
                       else
                         begin
                            s_mchan_cur_len <= cmd_count_i;
                            s_mchan_rem_len <= cmd_len_i;
                         end
                    end
                  else
                    begin
                       if ( (s_mchan_rem_len <= s_cmd_count) )
                         begin
                            s_mchan_cur_len  <= s_mchan_rem_len;
                            s_mchan_rem_len  <= 0;
                         end
                       else
                         begin
                            s_mchan_cur_len  <= s_cmd_count;
                            s_mchan_rem_len  <= s_mchan_rem_len - (s_cmd_count+1);
                         end
                    end
               end
          end
     end
   
   always_comb
     begin
        if ( ( s_mchan_rem_len <= s_cmd_count ) )
          begin
             s_trans_complete = 1;
          end
        else
          begin
             s_trans_complete = 0;
          end
     end
   
   //**********************************************************
   //****** COMPUTES THE EXT ADDRESS OF CURRENT TRANSACTION ***
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             s_mchan_ext_add <= '0;
          end
        else
          begin
             if ( cmd_req_i == 1'b1 ) // FIRST 2D TRANSFER
               begin
                  s_mchan_ext_add <= ext_add_i;
               end
             else
               begin
                  if ( cmd_req_o == 1 )
                    begin
                       s_mchan_ext_add <= s_mchan_ext_add + (s_cmd_stride + 1);
                    end
               end
          end
     end
   
   //**********************************************************
   //********** FINITE STATE MACHINE TO COMPUTE REQ ***********
   //**********************************************************
   
   // UPDATE THE STATE
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          CS <= TRANS_IDLE;
        else
          CS <= NS;
     end
   
   // COMPUTES NEXT STATE
   always_comb
     begin
        
        cmd_req_o = 0;
        
        case(CS)
          
          TRANS_IDLE:
            begin
               cmd_req_o = 0;
               if ( cmd_req_i == 1'b1 )
                 NS = TRANS_RUN;
               else
                 NS = TRANS_IDLE;
            end
          
          TRANS_RUN:
            begin
               cmd_req_o = 1;
               if ( s_trans_complete == 1'b1 || s_cmd_twd == 1'b0 )
                 begin
                    NS = TRANS_IDLE;
                 end
               else
                 begin
                    NS =  TRANS_RUN;
                 end
            end
          
          default:
            begin
               NS = TRANS_IDLE;
            end
          
        endcase
        
     end
   
   //**********************************************************
   //***** COMPUTE NUMBER OF COMMANDS *************************
   //**********************************************************
   
   // CHECKS BURST BOUNDARY CROSSING CONDITION
   always_comb
     begin
        if ( s_mchan_ext_add[EXT_ADD_WIDTH-1:$clog2(MCHAN_BURST_LENGTH)] != ( ( ( s_mchan_ext_add + ( s_mchan_cur_len + 1 ) ) -1 ) >>  $clog2(MCHAN_BURST_LENGTH) ) )
          s_ext_add_burst_crossed = 1'b1;
        else
          s_ext_add_burst_crossed = 1'b0;
     end
   
   // COMPUTE LENGTH OF FIRST TRANSFER
   always_comb
     begin
        if ( s_ext_add_burst_crossed == 1'b0  )
          s_mchan_first_len = s_mchan_cur_len; // BURST BOUNDARY NOT CROSSED
        else
          s_mchan_first_len = MCHAN_BURST_LENGTH - 1 - s_mchan_ext_add[$clog2(MCHAN_BURST_LENGTH)-1:0]; // BURST BOUNDARY CROSSED
     end
   
   assign s_mchan_init_rem_len      = s_mchan_cur_len - (s_mchan_first_len + 1);
   assign s_mchan_init_rem_len_plus = s_mchan_init_rem_len + 1;
   
   always_comb
     begin
        if ( s_mchan_init_rem_len_plus[$clog2(MCHAN_BURST_LENGTH)-1:0] == 0 )
          s_ext_add_burst_aligned = 1'b1;
        else
          s_ext_add_burst_aligned = 1'b0;
     end
   
   // COMPUTE NUMBER OF COMMANDS
   always_comb
     begin
        if ( s_ext_add_burst_crossed == 1'b0 )
          cmd_nb_o = 1;
        else
          if ( s_ext_add_burst_aligned == 1'b1 )
            cmd_nb_o = ( s_mchan_init_rem_len_plus >> $clog2(MCHAN_BURST_LENGTH) ) + 1;
          else
            cmd_nb_o = ( s_mchan_init_rem_len_plus >> $clog2(MCHAN_BURST_LENGTH) ) + 2;
     end
   
endmodule
