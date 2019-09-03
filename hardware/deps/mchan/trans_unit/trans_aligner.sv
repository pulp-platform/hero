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

module trans_aligner
  #(
    parameter MCHAN_LEN_WIDTH = 15
    )
   (
    input  logic                       clk_i,
    input  logic                       rst_ni,
    
    input  logic                       trans_req_i,
    output logic                       trans_gnt_o,
    input  logic [2:0]                 trans_pop_addr_i,
    input  logic [2:0]                 trans_push_addr_i,
    input  logic [MCHAN_LEN_WIDTH-1:0] trans_len_i,
    
    output logic [63:0]                data_pop_dat_o,
    output logic [7:0]                 data_pop_strb_o,
    input  logic                       data_pop_req_i,
    output logic                       data_pop_gnt_o,
    
    input  logic [63:0]                data_push_dat_i,
    input  logic                       data_push_req_i,
    output logic                       data_push_gnt_o
    );
   
   enum                                `ifdef SYNTHESIS logic [3:0] `endif { TRANS_IDLE, TRANS_FIRST, TRANS_SECOND, TRANS_THIRD, TRANS_RUN, PUSH_STALL, POP_STALL, TRANS_SSLAST, TRANS_SLAST, TRANS_LAST } CS, NS;
   
   logic [15:0][7:0]                   s_align_buffer;
   logic [7:0][3:0]                    s_even_align_matrix, s_odd_align_matrix, s_align_matrix;
   logic                               s_push_data, s_pop_data, s_push_align, s_pop_align, s_push_aligned, s_pop_aligned, s_pop_addr_greater;
   logic [2:0]                         s_pop_addr, s_push_addr;
   logic [7:0]                         s_first_strb, s_last_strb, s_single_strb;
   logic [MCHAN_LEN_WIDTH-1:0] 	       s_trans_len;
   logic [MCHAN_LEN_WIDTH-1:0]         s_beats_nb, s_push_beats_nb, s_push_beats_count, s_pop_beats_nb;
   logic                               s_start_count;
   logic                               s_store_strb;
   logic [7:0] 			       s_stall_strb;
   
   genvar                              j;
   
   //********************************************************
   //*********** ALIGNMENT CROSSBAR *************************
   //********************************************************
   
   generate
      
      for (j=0;j<8;j++)
      begin :  _ALIGNMENT_BUFFER_
        // ALIGNMENT BUFFER
        always_ff @ (posedge clk_i, negedge rst_ni)
          begin
             if (rst_ni == 1'b0)
               begin
                  s_align_buffer[j]   <= '0;
                  s_align_buffer[8+j] <= '0;
               end
             else
               begin
                  if (s_push_data == 1'b1)
                    begin
                       if (s_push_align == 1'b0)
                         begin
                            s_align_buffer[j]   <= data_push_dat_i[(8*(j+1))-1:8*j];
                         end
                       else
                         begin
                            s_align_buffer[8+j] <= data_push_dat_i[(8*(j+1))-1:8*j];
                         end
                    end
               end
          end
      end
      
   endgenerate
   
   // MUX TO DRIVE THE CROSSBAR
   always_comb
     begin
        if ( s_pop_align == 1'b1 )
          s_align_matrix = s_odd_align_matrix;
        else
          s_align_matrix = s_even_align_matrix;
     end
   
   // MUXES CROSSBAR
   generate
      
      for (j=0; j<8; j++)
        begin
           assign data_pop_dat_o[(8*(j+1))-1:8*j] = s_align_buffer[s_align_matrix[j]];
        end
      
   endgenerate
   
   //********************************************************
   //*********** CONTROL SIGNALS ****************************
   //********************************************************
   
   // REGISTER TO PUSH INPUT SIGNALS DURING THE TRANSACTION
   always_ff @ (posedge clk_i, negedge rst_ni)
   begin
        if (rst_ni == 1'b0)
          begin
             s_pop_addr  <= '0;
             s_push_addr <= '0;
             s_trans_len <= '0;
          end
        else
          begin
             if ( trans_req_i == 1'b1 && trans_gnt_o == 1'b1 )
               begin
                  s_pop_addr  <= trans_pop_addr_i;
                  s_push_addr <= trans_push_addr_i;
                  s_trans_len <= trans_len_i;
               end
          end
   end
   
   // GENERATION OF CONTROL SIGNALS FOR ALIGNMENT CROSSBAR
   generate
      for (j=0; j<8; j++)
        begin
           assign s_even_align_matrix[j] = j + s_push_addr - s_pop_addr;
           assign s_odd_align_matrix[j]  = 8 + j + s_push_addr - s_pop_addr;
        end
   endgenerate
   
   // GENERATION OF STROBE FOR FIRST BEAT
   assign s_first_strb = 8'b11111111 << s_pop_addr;
   
   // GENERATION OF STROBE SIGNAL FOR LAST BEAT
   assign s_last_strb   = 8'b11111111 >> ( 3'd7 - s_trans_len[2:0] - s_pop_addr);
   assign s_single_strb = 8'b11111111 >> ( 3'd7 - s_trans_len[2:0] )  << s_pop_addr;
   
   // COMPUTES NUMBER OF BEATS
   assign s_beats_nb = s_trans_len >> 3;
   
   //COMPUTES NUMBER OF PUSH BEATS AFTER ALIGNMENT
   always_comb
     begin
        if ( ( s_push_addr + s_trans_len[2:0] ) < 8 )
          begin
             s_push_aligned  = 1'b1;
             s_push_beats_nb = s_beats_nb;
          end
        else
          begin
             s_push_aligned  = 1'b0;
             s_push_beats_nb = s_beats_nb + 1;
          end
     end
   
   // COMPUTES NUMBER OF POP BEATS AFTER ALIGNMENT
   always_comb
     begin
        if ( ( s_pop_addr + s_trans_len[2:0] ) < 8 )
          begin
             s_pop_aligned  = 1'b1;
             s_pop_beats_nb = s_beats_nb;
          end
        else
          begin
             s_pop_aligned  = 1'b0;
             s_pop_beats_nb = s_beats_nb + 1;
          end
     end
   
   always_comb
     begin
        if ( s_pop_addr > s_push_addr )
          begin
             s_pop_addr_greater = 1'b1;
          end
        else
          begin
             s_pop_addr_greater = 1'b0;
          end
     end
   
   //COUNTER FOR NUMBER OF PUSH BEATS
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          s_push_beats_count <= 4'b0;
        else
          if ( s_start_count == 1'b1 )
            s_push_beats_count <= 4'b0;
          else
            if ( s_push_data == 1'b1 )
              s_push_beats_count <= s_push_beats_count+1;
            else
              s_push_beats_count <= s_push_beats_count;
     end
      
   // ALIGNMENT FLAGS
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          s_push_align <= 1'b0; // DEFAULT = EVEN
        else
          if (s_start_count == 1'b1)
            s_push_align <= 1'b0;
          else
            if (s_push_data == 1'b1)
              s_push_align <= !s_push_align;
     end
   
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          s_pop_align <= 1'b0; // DEFAULT = EVEN
        else
          if (s_start_count == 1'b1)
            s_pop_align <= 1'b0;
          else
            if (s_pop_data == 1'b1)
              s_pop_align <= !s_pop_align;
     end
   
   //********************************************************
   //*********** STORE STROBE WHEN STALLED ******************
   //********************************************************
   
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          s_stall_strb <= 0;
        else
          if (s_store_strb == 1'b1)
            s_stall_strb <= data_pop_strb_o;
     end
   
   //********************************************************
   //*********** PUSH INTERFACE FINITE STATE MACHINE ********
   //********************************************************
   
   // UPDATES THE STATE
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
        
        trans_gnt_o     = 1'b1;
        s_start_count   = 1'b0;
        data_push_gnt_o = 1'b0;
        data_pop_gnt_o  = 1'b0;
        s_push_data     = 1'b0;
        s_pop_data      = 1'b0;
        data_pop_strb_o = 8'b00000000;
	s_store_strb    = 1'b0;
        NS              = TRANS_IDLE;
        
        case(CS)
          
          TRANS_IDLE:
            begin
               data_push_gnt_o = 1'b0;
               data_pop_gnt_o  = 1'b0;
               if ( trans_req_i == 1'b1 )
                 begin
                    s_start_count   = 1'b1;
                    NS              = TRANS_FIRST;
                 end
               else
                 begin
                    NS = TRANS_IDLE;
                 end
            end
          
          TRANS_FIRST:
            begin
               trans_gnt_o     = 1'b0;
               data_push_gnt_o = 1'b1;
               data_pop_gnt_o  = 1'b0;
               data_pop_strb_o = 8'b00000000;
               if ( data_push_req_i == 1'b1 )
                 begin
                    s_push_data = 1'b1;
                    if ( s_push_beats_nb == 8'd0 )
                      begin
                         case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                           3'b000: NS = TRANS_LAST;
                           3'b001: NS = TRANS_LAST;
                           3'b010: NS = TRANS_SLAST;
                           3'b011: NS = TRANS_LAST;
                           3'b100: NS = TRANS_SLAST;
                           3'b101: NS = TRANS_LAST;
                           3'b110: NS = TRANS_SLAST;
                           3'b111: NS = TRANS_LAST;
                         endcase
                      end
                    else
                      begin
                         case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                           3'b000: NS = TRANS_SECOND;
                           3'b001: NS = TRANS_SECOND;
                           3'b010: NS = TRANS_THIRD;
                           3'b011: NS = TRANS_SECOND;
                           3'b100: NS = TRANS_THIRD;
                           3'b101: NS = TRANS_SECOND;
                           3'b110: NS = TRANS_THIRD;
                           3'b111: NS = TRANS_THIRD;
                         endcase
                      end
                 end
               else
                 begin
                    NS = TRANS_FIRST;
                 end
            end
          
          TRANS_SECOND:
            begin
               trans_gnt_o     = 1'b0;
               data_push_gnt_o = 1'b1;
               data_pop_gnt_o  = 1'b0;
               data_pop_strb_o = 8'b00000000;
               if ( data_push_req_i == 1'b1 )
                 begin
                    s_push_data = 1'b1;
                    if ( s_push_beats_nb == 8'd1 )
                      begin
                         case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                           3'b000: NS = TRANS_SLAST;
                           3'b001: NS = TRANS_LAST;
                           3'b010: NS = TRANS_SSLAST;
                           3'b011: NS = TRANS_SLAST;
                           3'b100: NS = TRANS_SSLAST;
                           3'b101: NS = TRANS_LAST;
                           3'b110: NS = TRANS_SSLAST;
                           3'b111: NS = TRANS_SSLAST;
                         endcase
                      end
                    else
                      begin
                         NS = TRANS_THIRD;
                      end
                 end
               else
                 begin
                    NS = TRANS_SECOND;
                 end
            end
          
          TRANS_THIRD:
            begin
               
               trans_gnt_o     = 1'b0;
               data_pop_gnt_o  = 1'b1;
               data_push_gnt_o = 1'b1;
               data_pop_strb_o = s_first_strb;
               
               case({data_push_req_i,data_pop_req_i})
                 
                 2'b00:
                   begin
                      NS = TRANS_RUN;
                   end
                 
                 2'b01:
                   begin
                      s_pop_data   = 1'b1;
		      s_store_strb = 1'b1;
                      NS = PUSH_STALL;
                   end
                 
                 2'b10:
                   begin
                      s_push_data    = 1'b1;
		      s_store_strb = 1'b1;
                      NS = POP_STALL;
                   end
                 
                 2'b11:
                   begin
                      s_push_data    = 1'b1;
                      s_pop_data     = 1'b1;
                      if ( s_push_beats_count == s_push_beats_nb )
                        begin
                           case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                             3'b000: NS = TRANS_SLAST;
                             3'b001: NS = TRANS_LAST;
                             3'b010: NS = TRANS_SLAST;
                             3'b011: NS = TRANS_SLAST;
                             3'b100: NS = TRANS_LAST;
                             3'b101: NS = TRANS_LAST;
                             3'b110: NS = TRANS_SLAST;
                             3'b111: NS = TRANS_LAST;
                           endcase
                        end
                      else
                        begin
                           NS = TRANS_RUN;
                        end
                   end
                 
                 default:
                   NS = TRANS_IDLE;
                 
               endcase
               
               if ( data_pop_req_i == 1'b0 )
                 begin
                    data_push_gnt_o = 1'b0;
                    s_push_data     = 1'b0;
                 end
               
            end
          
          TRANS_RUN:
            begin
               
               trans_gnt_o     = 1'b0;
               data_pop_gnt_o  = 1'b1;
               data_push_gnt_o = 1'b1;
               data_pop_strb_o = 8'b11111111;
               
               case({data_push_req_i,data_pop_req_i})
                 
                 2'b00:
                   begin
                      NS = TRANS_RUN;
                   end
                 
                 2'b01:
                   begin
                      s_pop_data = 1'b1;
		      s_store_strb = 1'b1;
                      NS = PUSH_STALL;
                   end
                 
                 2'b10:
                   begin
                      s_push_data  = 1'b1;
		      s_store_strb = 1'b1;
                      NS = POP_STALL;
                   end
                 
                 2'b11:
                   begin
                      s_push_data    = 1'b1;
                      s_pop_data     = 1'b1;
                      if ( s_push_beats_count == s_push_beats_nb )
                        begin
                           case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                             3'b000: NS = TRANS_SLAST;
                             3'b001: NS = TRANS_LAST;
                             3'b010: NS = TRANS_SLAST;
                             3'b011: NS = TRANS_SLAST;
                             3'b100: NS = TRANS_LAST;
                             3'b101: NS = TRANS_LAST;
                             3'b110: NS = TRANS_SLAST;
                             3'b111: NS = TRANS_LAST;
                           endcase
                        end
                      else
                        begin
                           NS = TRANS_RUN;
                        end
                   end
                 
                 default:
                   NS = TRANS_IDLE;
                 
               endcase
               
               if ( data_pop_req_i == 1'b0 )
                 begin
                    data_push_gnt_o = 1'b0;
                    s_push_data     = 1'b0;
                 end
               
            end
          
          PUSH_STALL:
            begin
               trans_gnt_o     = 1'b0;
               data_push_gnt_o = 1'b1;
               data_pop_gnt_o  = 1'b0;
               data_pop_strb_o = s_stall_strb;
               if( data_push_req_i == 1'b1 )
                 begin
                    s_push_data    = 1'b1;
                    if ( s_push_beats_count == s_push_beats_nb )
                      begin
                         case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                             3'b000: NS = TRANS_SLAST;
                             3'b001: NS = TRANS_LAST;
                             3'b010: NS = TRANS_SLAST;
                             3'b011: NS = TRANS_SLAST;
                             3'b100: NS = TRANS_LAST;
                             3'b101: NS = TRANS_LAST;
                             3'b110: NS = TRANS_SLAST;
                             3'b111: NS = TRANS_LAST;
                           endcase
                      end
                    else
                      begin
                         NS = TRANS_RUN;
                      end
                 end
               else
                 begin
                    NS = PUSH_STALL;
		    s_store_strb = 1'b1;
                 end
            end
          
          POP_STALL:
            begin
               trans_gnt_o     = 1'b0;
               data_push_gnt_o = 1'b0;
               s_push_data     = 1'b0;
               data_pop_gnt_o  = 1'b1;
               data_pop_strb_o = s_stall_strb;
               if( data_pop_req_i == 1'b1 )
                 begin
                    s_pop_data      = 1'b1;
                    s_push_data     = 1'b1;
                    data_push_gnt_o = 1'b1;
                    if ( s_push_beats_count == s_push_beats_nb )
                      begin
                         case({s_pop_addr_greater,s_push_aligned,s_pop_aligned})
                           3'b000: NS = TRANS_SLAST;
                           3'b001: NS = TRANS_LAST;
                           3'b010: NS = TRANS_SLAST;
                           3'b011: NS = TRANS_SLAST;
                           3'b100: NS = TRANS_LAST;
                           3'b101: NS = TRANS_LAST;
                           3'b110: NS = TRANS_SLAST;
                           3'b111: NS = TRANS_LAST;
                         endcase
                      end
                    else
                      begin
                         NS = TRANS_RUN;
                      end
                 end
               else
                 begin
                    NS = POP_STALL;
		    s_store_strb = 1'b1;
                 end
            end
          
          TRANS_SSLAST:
            begin
               trans_gnt_o     = 1'b0;
               data_pop_gnt_o  = 1'b1;
               data_push_gnt_o = 1'b0;
               data_pop_strb_o = 8'b11111111;
               
               if ( data_pop_req_i  == 1'b1 )
                 begin
                    s_pop_data = 1'b1;
                    NS         = TRANS_SLAST;
                 end
               else
                 begin
                    NS = TRANS_SSLAST;
                 end
            end
          
          TRANS_SLAST:
            begin
               trans_gnt_o     = 1'b0;
               data_pop_gnt_o  = 1'b1;
               data_push_gnt_o = 1'b0;
               
               if( s_pop_beats_nb == 8'd1 ) // if there is only one beat (and the pop address is not alinged) the strobe is s_first_strb
                 data_pop_strb_o = s_first_strb;
               else
                 data_pop_strb_o = 8'b11111111;
               
               if ( data_pop_req_i  == 1'b1 )
                 begin
                    s_pop_data = 1'b1;
                    NS         = TRANS_LAST;
                 end
               else
                 begin
                    NS = TRANS_SLAST;
                 end
            end
          
          TRANS_LAST:
            begin
               trans_gnt_o     = 1'b0;
               data_pop_gnt_o  = 1'b1;
               data_push_gnt_o = 1'b0;
               
               if ( s_pop_beats_nb == 8'd0 )
                 begin
                    data_pop_strb_o = s_single_strb;
                 end
               else
                 begin
                    data_pop_strb_o = s_last_strb;
                 end
               
               if ( data_pop_req_i  == 1'b1 )
                 begin
                    trans_gnt_o = 1'b1;
                    s_pop_data  = 1'b1;
                    if ( trans_req_i == 1'b1 )
                      begin
                         s_start_count   = 1'b1;
                         NS              = TRANS_FIRST;
                      end
                    else
                      begin
                         NS              = TRANS_IDLE;
                      end
                 end
               else
                 begin
                    NS         = TRANS_LAST;
                 end
            end
          
          default:
            begin
               NS = TRANS_IDLE;
            end
          
        endcase
     end
   
endmodule
