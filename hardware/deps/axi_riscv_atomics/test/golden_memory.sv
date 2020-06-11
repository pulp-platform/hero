// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

package golden_model_pkg;

    class golden_memory #(
        parameter int unsigned MEM_ADDR_WIDTH = 20,
        parameter int unsigned MEM_DATA_WIDTH = 32,
        parameter int unsigned AXI_ADDR_WIDTH = 32,
        parameter int unsigned AXI_DATA_WIDTH = 32,
        parameter int unsigned AXI_ID_WIDTH_M = 8,
        parameter int unsigned AXI_ID_WIDTH_S = 16,
        parameter int unsigned AXI_USER_WIDTH = 0
    );

        localparam int unsigned MEM_OFFSET_BITS = $clog2(MEM_DATA_WIDTH/8);
        localparam int unsigned NUM_MAST_WIDTH  = AXI_ID_WIDTH_S-AXI_ID_WIDTH_M;

        // Static variable for memory
        // static logic [(2**MEM_ADDR_WIDTH)*(AXI_DATA_WIDTH/8)-1:0][7:0]  memory;
        static logic [(2**MEM_ADDR_WIDTH)-1:0][7:0] memory;

        // AXI Bus to actual memory (after memory AXI-buffer)
        // This bus is only read to get the same linearization
        // in both the actual memory and the golden model.
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
          .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
          .AXI_ID_WIDTH  (AXI_ID_WIDTH_S),
          .AXI_USER_WIDTH(AXI_USER_WIDTH)
        ) axi;

        function new(virtual AXI_BUS_DV #(
                .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
                .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
                .AXI_ID_WIDTH  (AXI_ID_WIDTH_S),
                .AXI_USER_WIDTH(AXI_USER_WIDTH)
            ) axi
        );
            this.axi = axi;
            void'(randomize(memory));
        endfunction : new

        function automatic logic [MEM_ADDR_WIDTH-1:0] calculate_address(logic [AXI_ADDR_WIDTH-1:0] addr );
            // Crop address
            calculate_address = addr[MEM_ADDR_WIDTH-1:0];
        endfunction : calculate_address

        function automatic logic [AXI_ADDR_WIDTH-1:0] calculate_dut_address(logic [AXI_ADDR_WIDTH-1:0] addr);
            // Shift address
            calculate_dut_address = {{$clog2(AXI_DATA_WIDTH/8){1'b0}}, addr[AXI_ADDR_WIDTH-1:$clog2(AXI_DATA_WIDTH/8)]};
        endfunction : calculate_dut_address

        function automatic logic [AXI_ID_WIDTH_S-1:0] slave_id(logic [AXI_ID_WIDTH_M-1:0] master_id, logic [NUM_MAST_WIDTH-1:0] master_channel);
            slave_id[AXI_ID_WIDTH_S-1:AXI_ID_WIDTH_M] = ~master_channel;
            slave_id[AXI_ID_WIDTH_M-1:0] = master_id;
        endfunction : slave_id

        /**
         * Take data that is MEM_DATA_WIDTH wide and cut it back to the specified size and optionally sign extend it
         */
        function automatic logic [MEM_DATA_WIDTH-1:0] crop_data(logic [MEM_DATA_WIDTH-1:0] data, logic [2:0] size, logic sign_ext = 0);
            int unsigned num_bytes = 2**size;
            logic sign             = data[(8*num_bytes)-1];

            if (sign && sign_ext) begin
                crop_data = '1;
            end else begin
                crop_data = '0;
            end
            // For loop necessary because SystemVerilog does not allow variable ranges
            for (int i = 0; i < num_bytes; i++) begin
                crop_data[i*8 +: 8] = data[i*8 +: 8];
            end
        endfunction : crop_data

        function void set_memory(logic [MEM_ADDR_WIDTH-1:0] addr, logic [MEM_DATA_WIDTH-1:0] data, logic [2:0] size);
            int unsigned num_bytes = 2**size;
            for (int i = 0; i < num_bytes; i++) begin
                memory[addr+i] = data[i*8 +: 8];
            end
        endfunction : set_memory

        function logic [MEM_DATA_WIDTH-1:0] get_memory(logic [MEM_ADDR_WIDTH-1:0] addr, logic [2:0] size);
            int unsigned num_bytes = 2**size;
            // void'(randomize(get_memory));
            get_memory = '0;
            for (int i = 0; i < num_bytes; i++) begin
                get_memory[i*8 +: 8] = memory[addr+i];
            end
        endfunction : get_memory

        task write(
            input  logic [AXI_ADDR_WIDTH-1:0] addr,
            input  logic [MEM_DATA_WIDTH-1:0] w_data,
            input  logic [2:0]                size,
            input  logic [AXI_ID_WIDTH_M-1:0] m_id,
            input  logic [NUM_MAST_WIDTH-1:0] master = 0,
            output logic [MEM_DATA_WIDTH-1:0] r_data,
            output logic [1:0]                b_resp,
            input  logic [5:0]                atop = 0
        );

            automatic logic unsigned [MEM_ADDR_WIDTH-1:0] address  = calculate_address(addr);

            automatic logic unsigned [MEM_DATA_WIDTH-1:0] data_ui  = $unsigned(crop_data(w_data, size));
            automatic logic unsigned [MEM_DATA_WIDTH-1:0] data_uo  = 0;
            automatic logic   signed [MEM_DATA_WIDTH-1:0] data_si  = $signed(crop_data(w_data, size, 1));
            automatic logic   signed [MEM_DATA_WIDTH-1:0] data_so  = 0;

            automatic logic          [AXI_ID_WIDTH_S-1:0] id = slave_id(m_id, master);
            automatic logic          [AXI_ID_WIDTH_S-1:0] trans_id = 1;

            b_resp = axi_pkg::RESP_OKAY;

            if (atop == 0) begin
                // Wait for the write
                wait_b(id);
                set_memory(address, w_data, size);
                r_data = '0;
            end else if (atop == axi_pkg::ATOP_ATOMICSWAP) begin
                // Wait for the write to happen
                wait_b(id);
                // Read before writing and then update memory
                r_data = get_memory(address, size);
                set_memory(address, w_data, size);
            end else if ((atop[5:3] == {axi_pkg::ATOP_ATOMICLOAD,  axi_pkg::ATOP_LITTLE_END}) ||
                         (atop[5:3] == {axi_pkg::ATOP_ATOMICSTORE, axi_pkg::ATOP_LITTLE_END})) begin
                // Wait for the write to happen
                wait_b(id);
                data_uo = $unsigned(get_memory(address, size));
                data_so = $signed(crop_data(get_memory(address, size), size, 1));

                r_data  = data_uo;

                // Write result
                unique case (atop[2:0])
                    axi_pkg::ATOP_ADD : begin
                        w_data = data_uo + w_data;
                    end
                    axi_pkg::ATOP_CLR : begin
                        w_data = data_uo & (~w_data);
                    end
                    axi_pkg::ATOP_EOR : begin
                        w_data = data_uo ^ w_data;
                    end
                    axi_pkg::ATOP_SET : begin
                        w_data = data_uo | w_data;
                    end
                    axi_pkg::ATOP_SMAX: begin
                        w_data = (data_so > data_si) ? data_uo : w_data;
                    end
                    axi_pkg::ATOP_SMIN: begin
                        w_data = (data_so > data_si) ? w_data : data_uo;
                    end
                    axi_pkg::ATOP_UMAX: begin
                        w_data = (data_uo > data_ui) ? data_uo : w_data;
                    end
                    axi_pkg::ATOP_UMIN: begin
                        w_data = (data_uo > data_ui) ? w_data : data_uo;
                    end
                    default: begin
                        w_data = data_uo;
                    end
                endcase

                set_memory(address, w_data, size);

            end else if (atop == 6'b000111) begin
                // LR/SC pair
                // Wait for LR
                read(addr, r_data, size, m_id, master);

                // Check reservation
                wait_write(addr, size, id, trans_id);
                if (trans_id != id) begin
                    // SC failed
                    b_resp = axi_pkg::RESP_OKAY;
                end else begin
                    // Success
                    wait_b(id);
                    set_memory(address, w_data, size);
                    b_resp = axi_pkg::RESP_EXOKAY;
                end
            end else begin
                b_resp = axi_pkg::RESP_SLVERR;
                r_data = '0;
            end

            r_data = crop_data(r_data, size);

        endtask : write

        task read(
            input  logic [AXI_ADDR_WIDTH-1:0] addr,
            output logic [MEM_DATA_WIDTH-1:0] r_data,
            input  logic [2:0]                size,
            input  logic [AXI_ID_WIDTH_M-1:0] id,
            input  logic [NUM_MAST_WIDTH-1:0] master = 0
        );
            // Calculate memory address
            automatic logic unsigned [MEM_ADDR_WIDTH-1:0] address = calculate_address(addr);
            // Wait until the transaction actually happens
            wait_read(addr, size, slave_id(id, master));
            // Read data from golden model
            r_data = crop_data(get_memory(address, size), size);
        endtask : read

        // Linearization Functions
        logic [AXI_ID_WIDTH_S-1:0] default_id = 0; // Systemverilog requires a assignable default value (required to make this argument optional)
        task wait_write(
            input logic [AXI_ADDR_WIDTH-1:0] addr,
            input logic [2:0]                size,
            input logic [AXI_ID_WIDTH_S-1:0] id,
            inout logic [AXI_ID_WIDTH_S-1:0] out_id=default_id
        );
            if (out_id) begin
                // Wait for a transaction to be through the memory controller's buffers and return its ID
                @(posedge axi.clk_i iff ((axi.aw_valid & axi.aw_ready) && (axi.aw_addr == calculate_dut_address(addr))));
                out_id = axi.aw_id;
            end else begin
                // Wait for the transaction to be through the memory controller's buffers
                @(posedge axi.clk_i iff ((axi.aw_valid & axi.aw_ready) && (axi.aw_id[AXI_ID_WIDTH_S-1:0] == id) && (axi.aw_addr == calculate_dut_address(addr))));
            end
        endtask : wait_write

        task wait_b(
            input logic [AXI_ID_WIDTH_S-1:0] id
        );
            // Wait for the transaction to be confirmed by the memory controller
            @(posedge axi.clk_i iff (axi.b_valid && (axi.b_id[AXI_ID_WIDTH_S-1:0] == id)));
        endtask : wait_b

        task wait_read(
            input logic [AXI_ADDR_WIDTH-1:0] addr,
            input logic [2:0]                size,
            input logic [AXI_ID_WIDTH_S-1:0] id
        );
            // Wait for the transaction to be through the memory controller's buffers
            @(posedge axi.clk_i iff ((axi.ar_valid & axi.ar_ready) && (axi.ar_id[AXI_ID_WIDTH_S-1:0] == id) && (axi.ar_addr == calculate_dut_address(addr))));
        endtask : wait_read

    endclass : golden_memory
endpackage : golden_model_pkg
