// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module REP_buffer_4
#(
  parameter DATAWIDTH = 64
)
(
   input   logic                  clk, 
   input   logic                  rst_n, 

   //PUSH SIDE
   input   logic [DATAWIDTH-1:0]  DATA_in, 
   input   logic                  VALID_in, 
   output  logic                  GRANT_out, 

   //POP SIDE
   output  logic [DATAWIDTH-1:0]  DATA_out, 
   output  logic                  VALID_out, 
   input   logic                  GRANT_in
);

   enum logic [2:0] {EMPTY, FULL_1 , FULL_2 , FULL_3 , FULL_ALL }  CS, NS;

   logic    [DATAWIDTH-1:0]        FF[2:0];
   logic    [DATAWIDTH-1:0]        mux_out;
   logic                           enable_0;
   logic                           enable_all;
   logic    [3:0]                  sel;

   //UPDATE STATE BLOCK
   always_ff @(posedge clk or negedge rst_n)
   begin: UPDATE_FSM_STATE
           if(rst_n == 1'b0)
              CS <= EMPTY;
           else
              CS <= NS;
   end


   //COMPUTE FSM NEXT_STATE
   always_comb
   begin: COMPUTE_FSM_NEXT_STATE
      case(CS)

          EMPTY: if(!VALID_in)
                    NS = EMPTY;
                 else
                    NS = FULL_1;

          FULL_1: if(!VALID_in && GRANT_in)
                      NS = EMPTY;
                   else
                      if((VALID_in && GRANT_in) || (~VALID_in && ~GRANT_in))
                         NS = FULL_1;
                      else
                         NS = FULL_2;

          FULL_2: if(!VALID_in && GRANT_in)
                      NS = FULL_1;
                    else
                      if((VALID_in && GRANT_in) || (!VALID_in && ~GRANT_in))
                         NS = FULL_2;
                      else
                         NS = FULL_3;

          FULL_3: if(!VALID_in && GRANT_in)
                      NS = FULL_2;
                    else
                      if((VALID_in && GRANT_in) || (!VALID_in && ~GRANT_in))
                         NS = FULL_3;
                      else
                         NS = FULL_ALL;

          FULL_ALL: if(~GRANT_in)
                        NS = FULL_ALL;
                    else
                        NS = FULL_3;


          default : NS = EMPTY;
      endcase
   end



   //COMPUTE FSM OUTPUTS
   always_comb
   begin: COMPUTE_FSM_OUTPUTS
      case(CS)

          EMPTY: begin
                    if(VALID_in)
                       enable_0 = 1'b1;
                    else
                       enable_0 = 1'b0;
                       
                    enable_all = 1'b0;
                    sel = 4'd1;
                    VALID_out = 1'b0;
                    GRANT_out = 1'b1;
                 end

          FULL_1: begin
                      if(VALID_in && GRANT_in)
                         enable_0 = 1'b1;
                      else
                         enable_0 = 1'b0;
                      if(VALID_in && ~GRANT_in)
                         enable_all = 1'b1;
                      else
                         enable_all = 1'b0;
                      sel = 4'd1;
                      VALID_out = 1'b1;
                      GRANT_out = 1'b1;
                   end

          FULL_2: begin
                       if(GRANT_in)
                          enable_0 = 1'b1;
                       else
                          enable_0 = 1'b0;
                      if(VALID_in)
                         enable_all = 1'b1;
                      else
                         enable_all = 1'b0;
                      sel = 4'd2;
                      VALID_out = 1'b1;
                      GRANT_out = 1'b1;
                    end

          FULL_3: begin
                       if(GRANT_in)
                          enable_0 = 1'b1;
                       else
                          enable_0 = 1'b0;
                      if(VALID_in)
                         enable_all = 1'b1;
                      else
                         enable_all = 1'b0;
                      sel = 4'd4;
                      VALID_out = 1'b1;
                      GRANT_out = 1'b1;
                    end

          FULL_ALL: begin
                         if(GRANT_in)
                            enable_0 = 1'b1;
                         else
                            enable_0 = 1'b0;
                         enable_all = 1'b0;
                         sel = 4'd8;
                         VALID_out = 1'b1;
                         GRANT_out = 1'b0;
                   end

          default : begin
                         enable_0   = 1'b0;
                         enable_all = 1'b0;
                         sel        = 4'd1;
                         VALID_out  = 1'b0;
                         GRANT_out  = 1'b1;
                    end
      endcase
   end




   //MULTIPLEXER
   always_comb
   begin
           case(sel)
            1 : begin
                       mux_out = DATA_in;
                end
            2 : begin
                       mux_out = FF[0];
                end
            4 : begin
                       mux_out = FF[1];
                end
            8 : begin
                       mux_out = FF[2];
                end
            default: begin
                        mux_out = 0;
                     end

      endcase
   end


   //UPDATE STATE BLOCK
   always_ff @(posedge clk , negedge rst_n)
   begin: UPDATE_STATE_BLOCK
           if(rst_n == 1'b0)
            begin
              FF[0] <= 0;
              FF[1] <= 0;
              FF[2] <= 0;
              DATA_out <= 0;
            end
           else
            begin
               if(enable_0 == 1'b1)
                  DATA_out <= mux_out;
                  
               if(enable_all == 1'b1)
                begin
                  FF[0] <= DATA_in;
                  FF[1] <= FF[0];
                  FF[2] <= FF[1];
                end
            end
   end
endmodule
