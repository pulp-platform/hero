// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module RefillTracker_4
#(
    parameter  ID_WIDTH   = 14
)
(
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic                      push_i,
    input  logic [ID_WIDTH-1:0]       push_ID_i,
    output logic                      push_full_o,

    input  logic                      pop_i,
    input  logic [ID_WIDTH-1:0]       pop_ID_i,
    output logic                      pop_empty_o,
    output logic                      pop_error_o,

    input  logic [ID_WIDTH-1:0]       RESP_check_ID_i,
    input  logic                      RESP_check_req_i,
    output logic                      RESP_check_is_valid_o
);


localparam  DEPTH  = 4;

integer i,j,k,z;

logic [DEPTH-1:0]                     check_Match_addr;

logic [$clog2(DEPTH)-1:0]             MATCH_index;

logic [DEPTH-1:0]                     LOOKUP_TABLE;
logic [ID_WIDTH-1:0]                  ID_TABLE[DEPTH-1:0];

  
logic [DEPTH-1:0]                     Match_RESP_addr;






always_ff @(posedge clk, negedge rst_n)
begin
  if(rst_n == 1'b0)
  begin
    for(i=0; i<DEPTH; i++)
    begin
      LOOKUP_TABLE[i] <= 1'b0;
      ID_TABLE[i]     <= '0;
    end
  end
  else
    begin

      if(pop_i)
      LOOKUP_TABLE[MATCH_index] <= 1'b0;
      else;


        casex(LOOKUP_TABLE)

        4'bxxx0 :
        begin
                if(push_i)
                begin
                  LOOKUP_TABLE[0] <= 1'b1;
                  ID_TABLE[0]     <= push_ID_i;
                end
        end

        4'bxx01 : 
        begin
                if(push_i)
                begin
                  LOOKUP_TABLE[1]<= 1'b1;
                  ID_TABLE[1]     <= push_ID_i;
                end
        end

        4'bx011 :
        begin
                if(push_i)
                begin
                  LOOKUP_TABLE[2]<= 1'b1;
                  ID_TABLE[2]     <= push_ID_i;
                end
        end

        4'b0111 : 
        begin
                if(push_i)
                begin
                  LOOKUP_TABLE[3] <= 1'b1;
                  ID_TABLE[3]     <= push_ID_i;
                end
        end

        4'b1111 : 
        begin
                    //LOOKUP_TABLE[11][4] <= 1'b1;
        end

        endcase

    end
end


assign push_full_o     = (&LOOKUP_TABLE) ? 1'b1 : 1'b0;


always_comb
begin
  if(pop_i & ~pop_empty_o & (|check_Match_addr))
      pop_error_o = 1'b0;
   else
      pop_error_o = 1'b1;
end

assign pop_empty_o     = (|LOOKUP_TABLE == 1'b0) ? 1'b1 : 1'b0;





    onehot_to_bin #(.ONEHOT_WIDTH(DEPTH)) OH_2_BIN_POP  (.onehot(check_Match_addr), .bin(MATCH_index) );
    
    always_comb
    begin
    //       check_Match_addr = '0;
      for(j=0; j<DEPTH; j++)
      begin
      if({LOOKUP_TABLE[j],ID_TABLE[j]} == {1'b1,pop_ID_i})
        begin
          check_Match_addr[j] = 1'b1;
        end
      else
        begin
          check_Match_addr[j] = 1'b0;
        end
      end
    end

    always_comb
    begin

      Match_RESP_addr = '0;

      if(RESP_check_req_i)
      begin

        for(z=0; z<DEPTH; z++)
        begin
          if({LOOKUP_TABLE[z],ID_TABLE[z]} == {1'b1,RESP_check_ID_i})
            begin
            Match_RESP_addr[z] = 1'b1;
            end
          else
            begin
            Match_RESP_addr[z] = 1'b0;
            end
        end

        RESP_check_is_valid_o = |Match_RESP_addr;
      end
      else
      begin
      RESP_check_is_valid_o = 1'b0;
      end
    end 

endmodule
