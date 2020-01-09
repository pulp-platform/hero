// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`timescale 1ns/1ps
module tgen_128
#(
   parameter FETCH_ADDR_WIDTH = 32,
   parameter FETCH_DATA_WIDTH = 128
)
(
   input  logic                            clk,
   input  logic                            rst_n,

   output logic                            fetch_req_o,
   output logic [FETCH_ADDR_WIDTH-1:0]     fetch_addr_o,
   input  logic                            fetch_gnt_i,
   input  logic                            fetch_rvalid_i,
   input  logic [FETCH_DATA_WIDTH-1:0]     fetch_rdata_i,

   input logic                             fetch_enable_i,
   output logic                            eoc_o
);

   logic [15:0]                         RANDOM_ADD;

   int unsigned i, count_trans = 0;
   
   localparam N_TRANS = 10000000;

   enum logic [1:0]  { IDLE, WAIT_RVALID, WAIT_GNT , DONE } CS, NS;

   logic [31:0] address[N_TRANS];

   initial
   begin
      for(i=0;i<N_TRANS;i++)
      begin
         address[i] = $random() & 32'h0000_0FF0;
      end
   end


   logic                            fetch_req_int;
   logic [FETCH_ADDR_WIDTH-1:0]     fetch_addr_int;

   assign #(0.1) fetch_req_o  = fetch_req_int;
   assign #(0.1) fetch_addr_o = fetch_addr_int;

   event fetch_granted;
   event reset_deasserted;

   always @(posedge clk)
   begin
      if(fetch_gnt_i & fetch_req_o)
       ->  fetch_granted;
   end

   always @(posedge clk)
   begin
      if(fetch_gnt_i & fetch_req_o)
                count_trans++;
   end

   always @(posedge clk)
   begin
      if(rst_n == 1'b1)
        ->  reset_deasserted;

   end


   initial
   begin
        

        @(reset_deasserted);
        @(negedge clk);
        @(negedge clk);
        @(negedge clk);
        @(negedge clk);
        @(negedge clk);
        @(negedge clk);
        @(negedge clk);
   end


   always_ff @(posedge clk, negedge rst_n) 
   begin
      if(~rst_n) 
      begin
         CS <= IDLE;
      end 
      else 
      begin
          CS <= NS;
      end
   end


   always_comb
   begin
      fetch_req_int   = 1'b0;
      fetch_addr_int  = address[count_trans];
      eoc_o           = 1'b0;



      case(CS)
         IDLE: 
         begin
            if(fetch_enable_i)
            begin
               fetch_req_int   = 1'b1;

               if(fetch_gnt_i)
                  NS = WAIT_RVALID;
               else
                  NS = IDLE;
            end
            else
            begin
                  NS = IDLE;
            end
         end

         WAIT_RVALID:
         begin

            if(fetch_rvalid_i)
            begin
                if(count_trans == N_TRANS-1 )
                begin
                  NS = DONE;
                  fetch_req_int = 1'b0;
                end
                else
                begin
                    fetch_req_int   = 1'b1;
                    
                    if(fetch_gnt_i)
                    begin
                       NS = WAIT_RVALID;
                    end
                    else
                    begin
                       NS = WAIT_GNT;
                    end
                end
            end
            else
            begin
                  NS = WAIT_RVALID;
                  fetch_req_int = 1'b0;
            end
         end
         
         WAIT_GNT:
         begin
            fetch_req_int   = 1'b1;
            if(fetch_gnt_i)
               NS = WAIT_RVALID;
            else
               NS = WAIT_GNT;
         end

         DONE:
         begin
          NS = DONE;
          eoc_o = 1'b1;
         end

      endcase // CS
   end


endmodule // tgen_emu
