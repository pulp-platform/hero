// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi_buffer_rab
  #(
    parameter DATA_WIDTH,
    parameter BUFFER_DEPTH
  )
  (
    input logic                   clk,
    input logic                   rstn,

    // Downstream port
    output logic [DATA_WIDTH-1:0] data_out,
    output logic                  valid_out,
    input  logic                  ready_in,

    // Upstream port
    input  logic                  valid_in,
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic                  ready_out
  );

  localparam integer LOG_BUFFER_DEPTH = $clog2(BUFFER_DEPTH);

    // Internal data structures
    reg [LOG_BUFFER_DEPTH - 1 : 0] pointer_in;   // location to which we last wrote
    reg [LOG_BUFFER_DEPTH - 1 : 0] pointer_out;  // location from which we last sent
    reg     [LOG_BUFFER_DEPTH : 0] elements;     // number of elements in the buffer
    reg       [DATA_WIDTH - 1 : 0] buffer [BUFFER_DEPTH - 1 : 0];

    wire full;

    integer loop1;

    assign full = (elements == BUFFER_DEPTH);

    always @(posedge clk or negedge rstn)
      begin: elements_sequential
        if (rstn == 1'b0)
          elements <= 0;
        else
        begin
          // ------------------
          // Are we filling up?
          // ------------------
          // One out, none in
          if (ready_in && valid_out && (!valid_in || full))
            elements <= elements - 1;
          // None out, one in
          else if ((!valid_out || !ready_in) && valid_in && !full)
            elements <= elements + 1;
          // Else, either one out and one in, or none out and none in - stays unchanged
        end
      end

    always @(posedge clk or negedge rstn)
      begin: buffers_sequential
        if (rstn == 1'b0)
        begin
          for (loop1 = 0 ; loop1 < BUFFER_DEPTH ; loop1 = loop1 + 1)
            buffer[loop1] <= 0;
        end
        else
        begin
          // Update the memory
          if (valid_in && !full)
            buffer[pointer_in] <= data_in;
        end
      end

    always @(posedge clk or negedge rstn)
      begin: sequential
        if (rstn == 1'b0)
        begin
          pointer_out <= 0;
          pointer_in <= 0;
        end
        else
        begin
          // ------------------------------------
          // Check what to do with the input side
          // ------------------------------------
          // We have some input, increase by 1 the input pointer
          if (valid_in && !full)
          begin
            if (pointer_in == $unsigned(BUFFER_DEPTH - 1))
              pointer_in <= 0;
            else
              pointer_in <= pointer_in + 1;
          end
          // Else we don't have any input, the input pointer stays the same

          // -------------------------------------
          // Check what to do with the output side
          // -------------------------------------
          // We had pushed one flit out, we can try to go for the next one
          if (ready_in && valid_out)
          begin
            if (pointer_out == $unsigned(BUFFER_DEPTH - 1))
              pointer_out <= 0;
            else
              pointer_out <= pointer_out + 1;
          end
          // Else stay on the same output location
        end
      end

    // Update output ports
    assign data_out = buffer[pointer_out];
    assign valid_out = (elements != 0);

    assign ready_out = ~full;

endmodule
