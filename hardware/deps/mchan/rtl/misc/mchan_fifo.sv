// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Igor Loi <igor.loi@unibo.it>
// Davide Rossi <davide.rossi@unibo.it>

`include "mchan_defines.sv"

module mchan_fifo 
  #(
    parameter           DATA_WIDTH = 0,
    parameter           DATA_DEPTH = 8
    )
   (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    //PUSH SIDE
    input  logic [DATA_WIDTH-1:0]   push_dat_i,
    input  logic                    push_req_i,
    output logic                    push_gnt_o,
    //POP SIDE
    output logic [DATA_WIDTH-1:0]   pop_dat_o,
    output logic                    pop_gnt_o,
    input  logic                    pop_req_i
    );
   
   // Local Parameter
   localparam                ADDR_DEPTH = $clog2(DATA_DEPTH);
   
   enum 			    `ifdef SYNTHESIS logic [1:0] `endif { EMPTY, FULL, MIDDLE } CS, NS;
   // Internal Signals
   
   logic [ADDR_DEPTH-1:0] 	    Pop_Pointer_CS,  Pop_Pointer_NS;
   logic [ADDR_DEPTH-1:0] 	    Push_Pointer_CS, Push_Pointer_NS;
   logic [DATA_WIDTH-1:0] 	    FIFO_REGISTERS[DATA_DEPTH-1:0];
   integer 			    i;
   
   
   
   // Parameter Check
   // synopsys translate_off
   initial
   begin : parameter_check
      integer param_err_flg;
      param_err_flg = 0;
      
      if (DATA_WIDTH < 1)
        begin
           param_err_flg = 1;
           $display("ERROR: %m :\n  Invalid value (%d) for parameter DATA_WIDTH (legal range: greater than 1)", DATA_WIDTH );
        end
      
      if (DATA_DEPTH < 1)
        begin
           param_err_flg = 1;
           $display("ERROR: %m :\n  Invalid value (%d) for parameter DATA_DEPTH (legal range: greater than 1)", DATA_DEPTH );
        end           
   end
   // synopsys translate_on
   
   
   
   // UPDATE THE STATE
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          begin
             CS              <= EMPTY;
             Pop_Pointer_CS  <= {ADDR_DEPTH {1'b0}};
             Push_Pointer_CS <= {ADDR_DEPTH {1'b0}};
          end
        else
          begin
             CS              <= NS;
             Pop_Pointer_CS  <= Pop_Pointer_NS;
             Push_Pointer_CS <= Push_Pointer_NS;
          end
     end
   
   // Compute Next State
   always_comb
     begin
        
        case(CS)
          
          EMPTY:
            begin
               push_gnt_o = 1'b1;
               pop_gnt_o = 1'b0;
               
               case(push_req_i)
                 
                 1'b0 : 
                   begin 
                      NS      = EMPTY;
                      Push_Pointer_NS = Push_Pointer_CS;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
                   end
                 
                 1'b1: 
                   begin 
                      NS      = MIDDLE;
                      Push_Pointer_NS = Push_Pointer_CS + 1'b1;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
                   end
                 
               endcase
               
            end
          
          MIDDLE:
            begin
               push_gnt_o = 1'b1;
               pop_gnt_o = 1'b1;
               
               case({push_req_i,pop_req_i})
                 
                 2'b01:
                   begin 
                      if((Pop_Pointer_CS == Push_Pointer_CS -1 ) || ((Pop_Pointer_CS == DATA_DEPTH-1) && (Push_Pointer_CS == 0) ))
                        NS      = EMPTY;
                      else
                        NS      = MIDDLE;
                      
                      Push_Pointer_NS = Push_Pointer_CS;
                      
                      if(Pop_Pointer_CS == DATA_DEPTH-1)
                        Pop_Pointer_NS  = 0;
                      else
                        Pop_Pointer_NS  = Pop_Pointer_CS + 1'b1;
                   end
                 
		 
                 2'b00 : 
                   begin 
                      NS      = MIDDLE;
                      Push_Pointer_NS = Push_Pointer_CS;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
                   end
                 
                 2'b11: 
                   begin                   
                      NS      = MIDDLE;
                      
                      if(Push_Pointer_CS == DATA_DEPTH-1)
                        Push_Pointer_NS = 0;
                      else
                        Push_Pointer_NS = Push_Pointer_CS + 1'b1;
                      
                      if(Pop_Pointer_CS == DATA_DEPTH-1)
                        Pop_Pointer_NS  = 0;
                      else
                        Pop_Pointer_NS  = Pop_Pointer_CS  + 1'b1;
                   end
                 
		 
                 2'b10:
                   begin                 
                      if(( Push_Pointer_CS == Pop_Pointer_CS - 1) || ( (Push_Pointer_CS == DATA_DEPTH-1) && (Pop_Pointer_CS == 0) ))
                        NS      = FULL;
                      else
                        NS    = MIDDLE;
                      
                      if(Push_Pointer_CS == DATA_DEPTH - 1)
                        Push_Pointer_NS = 0;
                      else
                        Push_Pointer_NS = Push_Pointer_CS + 1'b1;
                      
                      Pop_Pointer_NS  = Pop_Pointer_CS;
                   end
                 
               endcase             
            end
          
          FULL:
            begin
               push_gnt_o = 1'b0;
               pop_gnt_o = 1'b1;
               
               case(pop_req_i)
                 
                 1'b1: 
                   begin 
                      
                      NS      = MIDDLE;
                      
                      Push_Pointer_NS = Push_Pointer_CS;
                      
                      if(Pop_Pointer_CS == DATA_DEPTH-1)
			Pop_Pointer_NS  = 0;
                      else
			Pop_Pointer_NS  = Pop_Pointer_CS  + 1'b1;
                      
                   end
                 
                 1'b0:
                   begin 
                      NS      = FULL;
                      
                      Push_Pointer_NS = Push_Pointer_CS;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
                   end
                 
               endcase     
               
            end // end of FULL
          
          default :
            begin
               push_gnt_o = 1'b0;
               pop_gnt_o = 1'b0;
               NS = EMPTY;
               Pop_Pointer_NS = 0;
               Push_Pointer_NS = 0;
            end
          
        endcase
        
        
     end
   
   
   
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          begin
             for (i=0; i< DATA_DEPTH; i++)
               FIFO_REGISTERS[i] <= {DATA_WIDTH {1'b0}};
          end
        else
          if((push_gnt_o == 1'b1) && (push_req_i == 1'b1))
            FIFO_REGISTERS[Push_Pointer_CS] <= push_dat_i;
          else ;
     end
   
   assign pop_dat_o = FIFO_REGISTERS[Pop_Pointer_CS];
   
endmodule
