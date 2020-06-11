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

`timescale 10ps/10ps

`include "assign.svh"

module automatic tb_top;

    // Constants
    parameter NUM_MASTERS    = 32;
    parameter OFFSET         = 16;
    parameter MAX_TIMEOUT    = 1000; // Cycles

    parameter AXI_ADDR_WIDTH = 64;
    parameter AXI_DATA_WIDTH = 64;
    parameter AXI_ID_WIDTH_M = 8;
    parameter AXI_ID_WIDTH_S = AXI_ID_WIDTH_M + $clog2(NUM_MASTERS);
    parameter AXI_USER_WIDTH = 6;

    parameter SYS_DATA_WIDTH = 64;
    parameter SYS_OFFSET_BIT = $clog2(SYS_DATA_WIDTH/8);

    parameter MEM_ADDR_WIDTH = 18;
    parameter MEM_START_ADDR = 128'h0000_0000_0000_0000_0000_0000_0000_0000; //32'h1C00_0000;
    parameter MEM_END_ADDR   = 128'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF; //MEM_START_ADDR + (2**MEM_ADDR_WIDTH);

    // Signal declarations
    logic clk   = 0;
    logic rst_n = 0;

    // Testbench status
    logic finished = 0;
    int unsigned num_errors = 0;

    // AXI bus declarations
    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_S ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_mem();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_S ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_dut[0:0]();

    // Simulated clusters
    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_M ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_cl[NUM_MASTERS]();

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_M ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_cl_dv[NUM_MASTERS](
        .clk_i          ( clk            )
    );

    generate
        for (genvar i = 0; i < NUM_MASTERS; i++) begin
            `AXI_ASSIGN(axi_cl[i], axi_cl_dv[i]);
        end
    endgenerate

    // Module instantiation
    axi_node_intf_wrap #(
        .NB_MASTER      ( 1              ), // To Memory
        .NB_SLAVE       ( NUM_MASTERS    ), // From clusters
        .NB_REGION      ( 1              ),
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_M ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) i_axi_node (
        // Clock and Reset
        .clk            ( clk            ),
        .rst_n          ( rst_n          ),
        .test_en_i      ( 1'b0           ),
        // AXI
        .slave          ( axi_cl         ),
        .master         ( axi_dut        ),
        // Memory map
        .start_addr_i   ( MEM_START_ADDR ),
        .end_addr_i     ( MEM_END_ADDR   ),
        .valid_rule_i   ( 1'b1           )
    );

    // Memory accessible over AXI bus
    // The AXI addresses are byte-addressed and shifted
    // so the memory is word-addressed. The memory size
    // is 2^MEM_ADDR_WIDTH * AXI_DATA_WIDTH bits.
    axi_memory #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_S ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH ),
        .MEM_ADDR_WIDTH ( MEM_ADDR_WIDTH )
    ) i_axi_memory (
        .clk_i   ( clk     ),
        .rst_ni  ( rst_n   ),
        .slv     ( axi_mem )
    );

    // axi_riscv_amos_wrap #(
    axi_riscv_atomics_wrap #(
        .AXI_ADDR_WIDTH     ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH     ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH       ( AXI_ID_WIDTH_S ),
        .AXI_USER_WIDTH     ( AXI_USER_WIDTH ),
        .AXI_MAX_READ_TXNS  ( 31             ),
        .AXI_MAX_WRITE_TXNS ( 31             ),
        .RISCV_WORD_WIDTH   ( SYS_DATA_WIDTH )
    ) i_axi_atomic_adapter (
        .clk_i    ( clk        ),
        .rst_ni   ( rst_n      ),
        .mst      ( axi_mem    ),
        .slv      ( axi_dut[0] )
    );

    // AXI Testbench
    // AXI driver
    tb_axi_pkg::axi_access #(
        .AW( AXI_ADDR_WIDTH ),
        .DW( AXI_DATA_WIDTH ),
        .IW( AXI_ID_WIDTH_M ),
        .UW( AXI_USER_WIDTH ),
        .SW( SYS_DATA_WIDTH ),
        // .TA( 200ps          ),
        // .TT( 700ps          )
        .TA( 0ps          ),
        .TT( 900ps          )
    ) axi_dut_master[NUM_MASTERS];

    generate
        for (genvar i = 0; i < NUM_MASTERS; i++) begin : gen_axi_access
            initial begin
                axi_dut_master[i] = new(i, axi_cl_dv[i]);
            end
        end
    endgenerate

    // Golden model
    // The golden model memory's data width is the system data width
    // Therefore, the golden memory address width must be larger than the
    // actual memory's address width if the data width does not match.
    // This ensures that both memories can store the same amount of bits.
    localparam int unsigned GOLD_MEM_WIDTH = MEM_ADDR_WIDTH + $clog2(AXI_DATA_WIDTH/8) ;// + (AXI_DATA_WIDTH/SYS_DATA_WIDTH) - 1;

    golden_model_pkg::golden_memory #(
        .MEM_ADDR_WIDTH( GOLD_MEM_WIDTH ),
        .MEM_DATA_WIDTH( SYS_DATA_WIDTH ),
        .AXI_ADDR_WIDTH( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH_M( AXI_ID_WIDTH_M ),
        .AXI_ID_WIDTH_S( AXI_ID_WIDTH_S ),
        .AXI_USER_WIDTH( AXI_USER_WIDTH )
    ) gold_memory = new(i_axi_memory.axi_mem_int);

    // Generate clock
    localparam tCK = 1ns;

    initial begin : clk_gen
        #tCK;
        while (1) begin
            clk <= 1;
            #(tCK/2);
            clk <= 0;
            #(tCK/2);
        end
    end

    initial begin : rst_gen
        rst_n <= 0;
        @(posedge clk);
        #(tCK/2);
        rst_n <= 1;
    end

    initial $timeformat(-9, 2, " ns", 10);

    /*====================================================================
    =                                Main                                =
    ====================================================================*/
    initial begin : main
        // Initialize the AXI drivers
        for (int i = 0; i < NUM_MASTERS; i++) begin
            axi_dut_master[i].reset_master();
        end
        // Wait for reset
        @(posedge clk);
        wait (rst_n);
        // Run tests!
        // test_all_amos();
        test_same_address();
        test_amo_write_consistency();
        // test_interleaving(); // Only works on old memory controller
        // test_atomic_counter();
        random_amo();

        // overtake_r();

        finished = 1;
    end

    /*====================================================================
    =                               Timeout                              =
    ====================================================================*/
    initial begin : timeout_block
        // Signals to check
        automatic int unsigned timeout = 0;
        automatic logic [3:0] handshake = 0;
        // Check for timeout
        @(posedge clk);
        wait (rst_n);

        fork
            while (timeout < MAX_TIMEOUT) begin
                handshake = {axi_dut[0].aw_valid, axi_dut[0].aw_ready, axi_dut[0].ar_valid, axi_dut[0].ar_ready};
                #100ns;
                @(posedge clk);
                if (handshake != {axi_dut[0].aw_valid, axi_dut[0].aw_ready, axi_dut[0].ar_valid, axi_dut[0].ar_ready}) begin
                    timeout = 0;
                end else begin
                    timeout += 1;
                end
            end
            while (!finished) begin
                #100ns;
                @(posedge clk);
            end
        join_any

        if (finished && num_errors == 0) begin
            $display("\nSUCCESS\n");
        end else if (finished) begin
            $display("\nFINISHED\n");
            $display("Encountered %d errors.\n", num_errors);
        end else begin
            $display("\nTIMEOUT\n");
            $display("Encountered %d errors.\n", num_errors);
        end

        $stop;
    end

    /*====================================================================
    =                            Random tests                            =
    ====================================================================*/
    task automatic random_amo();

        $display("Test random atomic accesses...\n");

        // Create multiple drivers
        for (int i = 0; i < NUM_MASTERS; i++) begin
            fork
                automatic int m = i;
                begin
                    automatic logic [AXI_ADDR_WIDTH-1:0] address;
                    automatic logic [AXI_ID_WIDTH_M-1:0] id;
                    automatic logic [SYS_DATA_WIDTH-1:0] data_init;
                    automatic logic [SYS_DATA_WIDTH-1:0] data_amo;
                    automatic logic [2:0]                size;
                    automatic logic [5:0]                atop;

                    automatic logic [SYS_DATA_WIDTH-1:0] r_data;
                    automatic logic [SYS_DATA_WIDTH-1:0] exp_data;
                    automatic logic [SYS_DATA_WIDTH-1:0] act_data;
                    automatic logic [1:0]                b_resp;
                    automatic logic [1:0]                exp_b_resp;

                    // Make some non-atomic transactions
                    repeat (100) begin
                        void'(randomize(address));
                        void'(randomize(data_init));
                        void'(randomize(id));
                        size = $urandom_range(0,SYS_OFFSET_BIT);
                        create_consistent_transaction(address, size, 0);
                        // Write
                        fork
                            axi_dut_master[m].axi_write(address, data_init, size, id, r_data, b_resp);
                            gold_memory.write(address, data_init, size, id, m, exp_data, exp_b_resp);
                        join
                        assert(b_resp == exp_b_resp) else begin
                            $warning("B (0x%1x) did not match expected (0x%1x)", b_resp, exp_b_resp);
                            num_errors += 1;
                        end
                        // Read
                        fork
                            axi_dut_master[m].axi_read(address, act_data, size, id);
                            gold_memory.read(address, exp_data, size, id, m);
                        join
                        assert(act_data == exp_data) else begin
                            $warning("R (0x%x) did not match expected data (0x%x) at address 0x%x, size 0x%x", act_data, exp_data, address, size);
                            num_errors += 1;
                        end
                    end

                    repeat (500) @(posedge clk);
                    repeat (20000) begin
                        void'(randomize(address));
                        void'(randomize(data_init));
                        void'(randomize(data_amo));
                        void'(randomize(id));
                        void'(randomize(atop));
                        size = $urandom_range(0,SYS_OFFSET_BIT);

                        // Mix in some non-atomic accesses
                        if (atop[3] == 1'b1) begin
                            atop = 6'b0;
                        end
                        // Make transaction valid
                        create_consistent_transaction(address, size, atop);
                        // Execute a write with data init, a AMO with data_amo and read result
                        write_amo_read_cycle(m, address, data_init, data_amo, size, 0, atop);
                        // Wait a random amount of cycles
                        repeat ($urandom_range(100,1000)) @(posedge clk);
                    end
                end
            join_none
        end

        // Wait for all cores to finish
        wait fork;

    endtask : random_amo

    task automatic overtake_r();

        $display("Try to overtake R...\n");
        fork
            begin
                // Create writes to slow down other thread
                automatic logic [AXI_ADDR_WIDTH-1:0] address;
                automatic logic [AXI_ID_WIDTH_M-1:0] id;
                automatic logic [SYS_DATA_WIDTH-1:0] data_init;
                automatic logic [2:0]                size;
                automatic logic [SYS_DATA_WIDTH-1:0] r_data;
                automatic logic [1:0]                b_resp;

                void'(randomize(address));
                void'(randomize(data_init));
                void'(randomize(id));
                size = $urandom_range(0,SYS_OFFSET_BIT);
                create_consistent_transaction(address, size, 0);

                repeat (20000) begin
                    axi_dut_master[0].axi_write(address, data_init, size, id, r_data, b_resp);
                end
            end
            begin
                // Create AMOs
                automatic logic [AXI_ADDR_WIDTH-1:0] address;
                automatic logic [AXI_ID_WIDTH_M-1:0] id;
                automatic logic [SYS_DATA_WIDTH-1:0] data_init;
                automatic logic [SYS_DATA_WIDTH-1:0] data_amo;
                automatic logic [2:0]                size;
                automatic logic [5:0]                atop = 6'b100000;

                repeat (2000) begin
                    void'(randomize(address));
                    void'(randomize(data_init));
                    void'(randomize(data_amo));
                    void'(randomize(id));
                    size = $urandom_range(0,SYS_OFFSET_BIT);

                    // Make transaction valid
                    create_consistent_transaction(address, size, atop);
                    // Execute a write with data init, a AMO with data_amo and read result
                    write_amo_read_cycle(1, address, data_init, data_amo, size, id, atop);
                    // Wait a random amount of cycles
                    // repeat ($urandom_range(100,1000)) @(posedge clk);
                end
            end
        join

    endtask : overtake_r

    /*====================================================================
    =                         Hand crafted tests                         =
    ====================================================================*/
    task automatic test_all_amos();

        localparam AXI_OFFSET_BIT = $clog2(AXI_DATA_WIDTH/8);

        automatic logic [AXI_ADDR_WIDTH-1:0] address;
        automatic logic [AXI_ID_WIDTH_M-1:0] id;
        automatic logic [SYS_DATA_WIDTH-1:0] data_init;
        automatic logic [SYS_DATA_WIDTH-1:0] data_amo;
        automatic logic [2:0]                size;
        automatic logic [1:0]                atomic_transaction;
        automatic logic [2:0]                atomic_operation;
        automatic logic [5:0]                atop;

        $display("Test all possible amos with a single thread...\n");

        // There are 17 AMO instructions + regular write
        for (int i = 0; i < 18; i++) begin
            // Go through all atomic operations
            atomic_operation   = i % 8;
            if (i < 8) begin
                // Atomic load
                atomic_transaction = 2'b10;
            end else if (i < 16) begin
                // Atomic store
                atomic_transaction = 2'b01;
            end else if (i == 16) begin
                // Atomic swap
                atomic_transaction = 2'b11;
                atomic_operation   = 0;
            end else if (i == 17) begin
                // Atomic swap
                atomic_transaction = 2'b0;
                atomic_operation   = 0;
            end
            atop = {atomic_transaction, 1'b0, atomic_operation};

            // Check all possible sizes
            for (int j = 2; j <= SYS_OFFSET_BIT; j++) begin
                // AMOs need to have at least 4 bytes --> start with size = 2
                size = j;

                // Test all possible alignments
                for (int k = 0; k < AXI_DATA_WIDTH/8; k = k+(2**size)) begin

                    // Test instructions with all possible signed/unsigned combinations
                    for (int l = 0; l < 4; l++) begin
                        // Find MSB (size is log2(num_bytes))
                        int unsigned msb = 2**size * 8;
                        void'(randomize(address));
                        void'(randomize(data_init));
                        void'(randomize(data_amo));
                        void'(randomize(id));
                        address[AXI_OFFSET_BIT-1:0] = k;

                        case (l)
                            0 : begin
                                // unsigned/unsigned
                                data_init[msb-1] = 1'b0;
                                data_amo[msb-1]  = 1'b0;
                            end
                            1 : begin
                                // unsigned/signed
                                data_init[msb-1] = 1'b0;
                                data_amo[msb-1]  = 1'b1;
                            end
                            2 : begin
                                // signed/unsigned
                                data_init[msb-1] = 1'b1;
                                data_amo[msb-1]  = 1'b0;
                            end
                            3 : begin
                                // signed/signed
                                data_init[msb-1] = 1'b1;
                                data_amo[msb-1]  = 1'b1;
                            end
                        endcase

                        create_consistent_transaction(address, size, atop);
                        // $display("Test: AMO=%x, Size=%x, Offset=%x, Sign=%x: %x # %x @(%x)", i, j, k, l, data_init, data_amo, address);
                        write_amo_read_cycle(0, address, data_init, data_amo, size, 0, atop);

                    end
                end
            end
        end

    endtask : test_all_amos

    // Test if the adapter inserts the write request correctly
    // ! This only works with a memory controller that allows multiple outstanding transactions
    task automatic test_interleaving();
        // Parameters
        parameter NUM_BURSTS    = 4;
        parameter INIT_MEM_VAL  = 305419896; // 0x12345678
        parameter ATOP_OPERAND  = 43962;     // 0xABBA
        // Variables
        automatic int unsigned addr = MEM_START_ADDR;
        automatic logic [AXI_ID_WIDTH_M-1:0] id;
        automatic logic [SYS_DATA_WIDTH-1:0] r_data;
        automatic logic [2:0] size = SYS_OFFSET_BIT;
        automatic logic [SYS_DATA_WIDTH-1:0] exp_data;
        automatic logic [1:0] b_resp;
        automatic logic [1:0] exp_b_resp;

        automatic axi_test::axi_ax_beat #(.AW(AXI_ADDR_WIDTH), .IW(AXI_ID_WIDTH_M), .UW(AXI_USER_WIDTH)) ax_beat = new;
        automatic axi_test::axi_r_beat  #(.DW(AXI_DATA_WIDTH), .IW(AXI_ID_WIDTH_M), .UW(AXI_USER_WIDTH))  r_beat = new;
        automatic axi_test::axi_w_beat  #(.DW(AXI_DATA_WIDTH), .UW(AXI_USER_WIDTH)) w_beat = new;
        automatic axi_test::axi_b_beat  #(.IW(AXI_ID_WIDTH_M), .UW(AXI_USER_WIDTH)) b_beat = new;

        $display("Test interleaving of write accesses...\n");

        // Initialize memory with 0x12345678 + i
        for (int i = 0; i < 3*NUM_BURSTS; i++) begin
            addr = MEM_START_ADDR + (i*SYS_DATA_WIDTH/8);
            axi_dut_master[i].axi_write(addr, INIT_MEM_VAL + i, size, 1, r_data, b_resp);
        end

        ax_beat.ax_size = size;
        ax_beat.ax_atop = 6'b000000;
        // Generate lots of write requests without sending the data yet
        for (int i = 1; i < NUM_BURSTS; i++) begin
            // Generate AW request
            ax_beat.ax_addr = MEM_START_ADDR + (i*AXI_DATA_WIDTH/8);;
            void'(randomize(id));
            ax_beat.ax_id = id;
            axi_dut_master[i].send_aw(ax_beat);
        end

        // Generate an ATOP request
        ax_beat.ax_addr = MEM_START_ADDR;
        ax_beat.ax_atop = 6'b100000;
        void'(randomize(id));
        ax_beat.ax_id   = id;
        axi_dut_master[0].send_aw(ax_beat);
        // Reset ATOP to regular requests
        ax_beat.ax_atop = 6'b000000;

        // Accept the R response
        fork
            begin
                axi_dut_master[0].recv_r(r_beat);
                r_data = r_beat.r_data[SYS_DATA_WIDTH-1:0];
                if (r_data != INIT_MEM_VAL) begin
                    $display("Test interleaving: ATOP R response was %x. Exp %x", r_data, INIT_MEM_VAL);
                end
            end
        join_none

        // Generate lots of write requests without sending the data yet
        for (int i = NUM_BURSTS; i < 2*NUM_BURSTS; i++) begin
            // Generate AW request
            ax_beat.ax_addr = MEM_START_ADDR + (i*AXI_DATA_WIDTH/8);;
            void'(randomize(id));
            ax_beat.ax_id = id;
            axi_dut_master[i].send_aw(ax_beat);
        end

        fork
            begin
                // Send W data for AMO
                w_beat.w_data = ATOP_OPERAND;
                w_beat.w_last = '1;
                w_beat.w_strb = '0;
                w_beat.w_strb = {{SYS_DATA_WIDTH/8}{1'b1}};
                axi_dut_master[0].send_w(w_beat);
            end
        join_none

        // Keep sending requests and data
        fork
            // Generate further AW requests
            for (int i = 2*NUM_BURSTS; i < 3*NUM_BURSTS; i++) begin
                // Generate AW request
                ax_beat.ax_addr = MEM_START_ADDR + (i*AXI_DATA_WIDTH/8);
                void'(randomize(id));
                ax_beat.ax_id = id;
                axi_dut_master[i].send_aw(ax_beat);
                @(posedge clk);
            end
            // Send the W data
            fork
                for (int i = 1; i < 3*NUM_BURSTS; i++) begin
                    // Generate W request
                    w_beat.w_data = i;
                    w_beat.w_last = '1;
                    w_beat.w_strb = '0;
                    w_beat.w_strb = {{SYS_DATA_WIDTH/8}{1'b1}};
                    axi_dut_master[i].send_w(w_beat);
                    @(posedge clk);
                    @(posedge clk);
                end
            join_none
            // Accept the B response
            for (int i = 0; i < 3*NUM_BURSTS; i++) begin
                fork
                    automatic int j = i;
                    automatic axi_test::axi_b_beat  #(.IW(AXI_ID_WIDTH_M), .UW(AXI_USER_WIDTH)) b_beat_temp = new;
                        axi_dut_master[j].recv_b(b_beat_temp);
                join_none
            end
        join

        // Wait for AMO to finish
        wait fork;

        // Check result
        // Read result of ATOP
        ax_beat.ax_addr = MEM_START_ADDR;
        void'(randomize(id));
        ax_beat.ax_id = id;
        axi_dut_master[0].send_ar(ax_beat);
        axi_dut_master[0].recv_r(r_beat);
        r_data = r_beat.r_data[SYS_DATA_WIDTH-1:0];

        if (r_data != (INIT_MEM_VAL + ATOP_OPERAND)) begin
            $display("Test interleaving: ATOP result is %x. Exp %x", r_data, INIT_MEM_VAL + ATOP_OPERAND);
        end

        // Read all other writes
        for (int i = 1; i < 3*NUM_BURSTS; i++) begin
            // Generate AW request
            ax_beat.ax_addr = MEM_START_ADDR + (i*AXI_DATA_WIDTH/8);;
            void'(randomize(id));
            ax_beat.ax_id = id;
            axi_dut_master[i].send_ar(ax_beat);
            axi_dut_master[i].recv_r(r_beat);
            r_data = r_beat.r_data[SYS_DATA_WIDTH-1:0];
            if (r_data != i) begin
                $display("Test interleaving: Write result is %x. Exp %x", r_data, i);
            end
        end

        #1000ns;

    endtask : test_interleaving

    // Test multiple atomic accesses to the same address
    task automatic test_atomic_counter();
        // Parameters
        parameter NUM_ITERATION = 100;
        parameter COUNTER_ADDR  = 'h01002000;
        // Variables
        automatic logic [SYS_DATA_WIDTH-1:0] r_data;
        automatic logic [2:0] size = SYS_OFFSET_BIT;
        automatic logic [1:0] b_resp;

        $display("Run atomic counter...\n");

        // Initialize to zero
        axi_dut_master[0].axi_write(COUNTER_ADDR, 0, size, 0, r_data, b_resp, 6'b000000);

        // Create multiple drivers
        for (int i = 0; i < NUM_MASTERS; i++) begin
            fork
                automatic int m = i;
                for (int i = 0; i < NUM_ITERATION; i++) begin
                    axi_dut_master[m].axi_write(COUNTER_ADDR, 1, size, m, r_data, b_resp, 6'b100000);
                end
            join_none
        end

        // Wait for all cores to finish
        wait fork;

        // Check result
        axi_dut_master[0].axi_read(COUNTER_ADDR, r_data, size, 0);

        if (r_data == NUM_ITERATION*NUM_MASTERS) begin
            $display("Adder result correct: %d", r_data);
        end else begin
            $display("Adder result wrong: %d (Expected: %d)", r_data, NUM_ITERATION*NUM_MASTERS);
        end

    endtask : test_atomic_counter

    // Test if the adapter protects the atomic region correctly
    task automatic test_same_address();
        // Parameters
        parameter NUM_ITERATION = 10;
        parameter ADDRESS = 'h01004000;
        // Variables
        automatic logic [AXI_ADDR_WIDTH-1:0] address = ADDRESS; // shared by all threads
        automatic logic [SYS_DATA_WIDTH-1:0] r_data_init;
        automatic logic [1:0] b_resp_init;
        automatic logic [SYS_DATA_WIDTH-1:0] exp_data_init;
        automatic logic [1:0] exp_b_resp_init;

        $display("Test random accesses to the same memory location...\n");

        // Initialize memory with 0
        fork
            axi_dut_master[0].axi_write(address, 0, SYS_OFFSET_BIT, 1, r_data_init, b_resp_init);
            gold_memory.write(address, 0, SYS_OFFSET_BIT, 1, 0, exp_data_init, exp_b_resp_init);
        join

        // Spawn multiple processes accessing this address
        for (int i = 0; i < NUM_MASTERS; i++) begin
            fork
                automatic int m = i;
                automatic logic [SYS_OFFSET_BIT-1:0] addr_range;
                automatic logic [AXI_ID_WIDTH_M-1:0] id;
                automatic logic [AXI_ID_WIDTH_S-1:0] s_id;
                automatic logic [SYS_DATA_WIDTH-1:0] w_data;
                automatic logic [2:0]                size = 3'b011;
                automatic logic [SYS_DATA_WIDTH-1:0] r_data;
                automatic logic [SYS_DATA_WIDTH-1:0] exp_data;
                automatic logic [1:0] b_resp;
                automatic logic [1:0] exp_b_resp;
                automatic logic [5:0] atop;
                for (int j = 0; j < NUM_ITERATION; j++) begin
                    // Randomize address but keep it in same word
                    void'(randomize(addr_range));
                    address = ADDRESS + addr_range;
                    void'(randomize(id));
                    void'(randomize(w_data));
                    void'(randomize(atop));
                    void'(randomize(size));
                    size = 3'b011;
                    if (atop[3] | (&atop[5:4] & |atop[2:0])) begin
                        atop = 6'b000000;
                    end
                    create_consistent_transaction(address, size, atop);
                    fork
                        axi_dut_master[m].axi_write(address, w_data, size, id, r_data, b_resp, atop);
                        gold_memory.write(address, w_data, size, id, m, exp_data, exp_b_resp, atop);
                    join
                    assert(b_resp == exp_b_resp) else begin
                        $warning("B (0x%1x) did not match expected (0x%1x)", b_resp, exp_b_resp);
                        num_errors += 1;
                    end
                    if ((atop[5:3] == {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END}) |
                        (atop[5:3] == {axi_pkg::ATOP_ATOMICSWAP, axi_pkg::ATOP_LITTLE_END})) begin
                        assert(r_data == exp_data) else begin
                            $warning("ATOP (0x%x) did not match expected data (0x%x) at address 0x%x at operation: 0x%2x", r_data, exp_data, address, atop);
                            num_errors += 1;
                        end
                    end
                end
            join_none
        end

        // Wait for all cores to finish
        wait fork;

        #1000ns;

    endtask : test_same_address

    // Test if the adapter protects the atomic region correctly
    task automatic test_amo_write_consistency();
        // Parameters
        parameter NUM_ITERATION = 200;
        parameter ADDRESS_START = 'h01004000;
        parameter ADDRESS_END   = 'h01004040;
        // Variables
        automatic logic [AXI_ADDR_WIDTH-1:0] address = ADDRESS_START; // shared by all threads
        automatic logic [SYS_DATA_WIDTH-1:0] r_data_init;
        automatic logic [1:0] b_resp_init;
        automatic logic [SYS_DATA_WIDTH-1:0] exp_data_init;
        automatic logic [1:0] exp_b_resp_init;

        $display("Test AMO and write consistency...\n");

        // Initialize memory with 0
        for (int i = 0; i < (ADDRESS_END-ADDRESS_START)/(SYS_DATA_WIDTH/8); i+=(SYS_DATA_WIDTH/8)) begin
            write_amo_read_cycle(0, ADDRESS_START+i, 0, 0, SYS_OFFSET_BIT, 0, 0);
        end

        // Spawn multiple processes accessing this address
        for (int i = 0; i < NUM_MASTERS; i++) begin
            fork
                automatic int m = i;
                automatic logic [AXI_ADDR_WIDTH-1:0] address;
                automatic logic [AXI_ID_WIDTH_M-1:0] id;
                automatic logic [SYS_DATA_WIDTH-1:0] data_init;
                automatic logic [SYS_DATA_WIDTH-1:0] data_amo;
                automatic logic [2:0]                size;
                automatic logic [5:0]                atop;
                for (int j = 0; j < NUM_ITERATION; j++) begin
                    // Randomize address but keep it in same word
                    address = $urandom_range(ADDRESS_START,ADDRESS_END);
                    void'(randomize(id));
                    void'(randomize(data_init));
                    void'(randomize(data_amo));
                    void'(randomize(atop));
                    atop = create_valid_atop();
                    // void'(randomize(size)); // Half-word not supported by LRSC yet
                    size = SYS_OFFSET_BIT;
                    create_consistent_transaction(address, size, atop);
                    write_amo_read_cycle(m, address, data_init, data_amo, size, id, atop);
                end
            join_none
        end

        // Wait for all cores to finish
        wait fork;

        #1000ns;

    endtask : test_amo_write_consistency

    /*====================================================================
    =                          Helper Functions                          =
    ====================================================================*/
    task automatic create_consistent_transaction(
        inout logic [AXI_ADDR_WIDTH-1:0] address,
        inout logic [2:0]                size,
        input logic [5:0]                amo
    );
        // Transaction must be single burst --> max size is system size
        if (size > SYS_OFFSET_BIT) begin
            size = SYS_OFFSET_BIT;
        end

        // AMO transactions need to be 4 bytes at least
        if ((size < 3'b010) && amo) begin
            size = 3'b010;
        end

        // Address needs to by size aligned
        if (size) begin
            // At least two bytes --> alignment necessary
            for (int i = 0; i < size; i++) begin
                address[i] = 1'b0;
            end
        end
    endtask : create_consistent_transaction

    function automatic logic [5:0] create_valid_atop();
        int random_atop = $urandom_range(0, 16);
        void'(randomize(create_valid_atop));

        if (random_atop < 8) begin
            // Store
            create_valid_atop[5:3] = 3'b010;
        end else if (random_atop < 16) begin
            // Load
            create_valid_atop[5:3] = 3'b100;
        end else begin
            create_valid_atop = 6'b110000;
        end
    endfunction : create_valid_atop

    task automatic write_cycle(
        input int unsigned               driver,
        input logic [AXI_ADDR_WIDTH-1:0] address,
        input logic [SYS_DATA_WIDTH-1:0] data,
        input logic [SYS_DATA_WIDTH-1:0] data_amo,
        input logic [2:0]                size,
        input logic [AXI_ID_WIDTH_M-1:0] id,
        input logic [5:0]                atop
    );
        automatic logic [AXI_ID_WIDTH_M-1:0] trans_id = id;
        automatic logic [SYS_DATA_WIDTH-1:0] r_data;
        automatic logic [SYS_DATA_WIDTH-1:0] exp_data;
        automatic logic [SYS_DATA_WIDTH-1:0] act_data;
        automatic logic [1:0]  b_resp;
        automatic logic [1:0]  exp_b_resp;

        // Write (Need valid memory for atop)
        if (!id) begin
            void'(randomize(trans_id));
        end
        fork
            axi_dut_master[driver].axi_write(address, data, size, trans_id, r_data, b_resp);
            gold_memory.write(address, data, size, trans_id, driver, exp_data, exp_b_resp);
        join
        // AMO
        if (!id) begin
            void'(randomize(trans_id));
        end
        fork
            // Atomic operation
            axi_dut_master[driver].axi_write(address, data_amo, size, trans_id, r_data, b_resp, atop);
            // Golden model
            gold_memory.write(address, data_amo, size, trans_id, driver, exp_data, exp_b_resp, atop);
        join
        assert(b_resp == exp_b_resp) else begin
            $warning("B (0x%1x) did not match expected (0x%1x)", b_resp, exp_b_resp);
            num_errors += 1;
        end
        if ((atop[5:3] == {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END}) |
            (atop[5:3] == {axi_pkg::ATOP_ATOMICSWAP, axi_pkg::ATOP_LITTLE_END})) begin
            assert(r_data == exp_data) else begin
                $warning("ATOP (0x%x) did not match expected data (0x%x) at address 0x%x at operation: 0x%2x", r_data, exp_data, address, atop);
                num_errors += 1;
            end
        end
        // Read result
        if (!id) begin
            void'(randomize(trans_id));
        end
        fork
            axi_dut_master[driver].axi_read(address, act_data, size, trans_id);
            gold_memory.read(address, exp_data, size, trans_id, driver);
        join
        assert(act_data == exp_data) else begin
            $warning("R (0x%x) did not match expected data (0x%x) at address 0x%x, size %x, after operation: 0x%2x (0x%x)", act_data, exp_data, address, size, atop, data);
            num_errors += 1;
        end
    endtask : write_cycle

    task automatic write_amo_read_cycle(
        input int unsigned               driver,
        input logic [AXI_ADDR_WIDTH-1:0] address,
        input logic [SYS_DATA_WIDTH-1:0] data_init,
        input logic [SYS_DATA_WIDTH-1:0] data_amo,
        input logic [2:0]                size,
        input logic [AXI_ID_WIDTH_M-1:0] id,
        input logic [5:0]                atop
    );
        automatic logic [AXI_ID_WIDTH_M-1:0] trans_id = id;
        automatic logic [SYS_DATA_WIDTH-1:0] r_data;
        automatic logic [SYS_DATA_WIDTH-1:0] exp_data;
        automatic logic [SYS_DATA_WIDTH-1:0] act_data;
        automatic logic [1:0]  b_resp;
        automatic logic [1:0]  exp_b_resp;

        // Write (Need valid memory for atop)
        if (!id) begin
            void'(randomize(trans_id));
        end
        fork
            axi_dut_master[driver].axi_write(address, data_init, size, trans_id, r_data, b_resp);
            gold_memory.write(address, data_init, size, trans_id, driver, exp_data, exp_b_resp);
        join
        // AMO
        if (!id) begin
            void'(randomize(trans_id));
        end
        fork
            // Atomic operation
            axi_dut_master[driver].axi_write(address, data_amo, size, trans_id, r_data, b_resp, atop);
            // Golden model
            gold_memory.write(address, data_amo, size, trans_id, driver, exp_data, exp_b_resp, atop);
        join
        assert(b_resp == exp_b_resp) else begin
            $warning("B (0x%1x) did not match expected (0x%1x)", b_resp, exp_b_resp);
            num_errors += 1;
        end
        if ((atop[5:3] == {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END}) |
            (atop[5:3] == {axi_pkg::ATOP_ATOMICSWAP, axi_pkg::ATOP_LITTLE_END})) begin
            assert(r_data == exp_data) else begin
                $warning("ATOP (0x%x) did not match expected data (0x%x) at address 0x%x at operation: 0x%2x", r_data, exp_data, address, atop);
                num_errors += 1;
            end
        end
        // Read result
        if (!id) begin
            void'(randomize(trans_id));
        end
        fork
            axi_dut_master[driver].axi_read(address, act_data, size, trans_id);
            gold_memory.read(address, exp_data, size, trans_id, driver);
        join
        assert(act_data == exp_data) else begin
            $warning("R (0x%x) did not match expected data (0x%x) at address 0x%x, size %x, after operation: 0x%2x (0x%x)", act_data, exp_data, address, size, atop, data_init);
            num_errors += 1;
        end
    endtask : write_amo_read_cycle

    /*====================================================================
    =                        AXI Protocol checker                        =
    ====================================================================*/
    logic [AXI_ADDR_WIDTH-1:0]   axi_mem_aw_addr;
    logic [2:0]                  axi_mem_aw_prot;
    logic [3:0]                  axi_mem_aw_region;
    logic [5:0]                  axi_mem_aw_atop;
    logic [7:0]                  axi_mem_aw_len;
    logic [2:0]                  axi_mem_aw_size;
    logic [1:0]                  axi_mem_aw_burst;
    logic                        axi_mem_aw_lock;
    logic [3:0]                  axi_mem_aw_cache;
    logic [3:0]                  axi_mem_aw_qos;
    logic [AXI_ID_WIDTH_S-1:0]   axi_mem_aw_id;
    logic [AXI_USER_WIDTH-1:0]   axi_mem_aw_user;
    logic                        axi_mem_aw_ready;
    logic                        axi_mem_aw_valid;
    logic [AXI_ADDR_WIDTH-1:0]   axi_mem_ar_addr;
    logic [2:0]                  axi_mem_ar_prot;
    logic [3:0]                  axi_mem_ar_region;
    logic [7:0]                  axi_mem_ar_len;
    logic [2:0]                  axi_mem_ar_size;
    logic [1:0]                  axi_mem_ar_burst;
    logic                        axi_mem_ar_lock;
    logic [3:0]                  axi_mem_ar_cache;
    logic [3:0]                  axi_mem_ar_qos;
    logic [AXI_ID_WIDTH_S-1:0]   axi_mem_ar_id;
    logic [AXI_USER_WIDTH-1:0]   axi_mem_ar_user;
    logic                        axi_mem_ar_ready;
    logic                        axi_mem_ar_valid;
    logic [AXI_DATA_WIDTH-1:0]   axi_mem_w_data;
    logic [AXI_DATA_WIDTH/8-1:0] axi_mem_w_strb;
    logic [AXI_USER_WIDTH-1:0]   axi_mem_w_user;
    logic                        axi_mem_w_last;
    logic                        axi_mem_w_ready;
    logic                        axi_mem_w_valid;
    logic [AXI_DATA_WIDTH-1:0]   axi_mem_r_data;
    logic [1:0]                  axi_mem_r_resp;
    logic                        axi_mem_r_last;
    logic [AXI_ID_WIDTH_S-1:0]   axi_mem_r_id;
    logic [AXI_USER_WIDTH-1:0]   axi_mem_r_user;
    logic                        axi_mem_r_ready;
    logic                        axi_mem_r_valid;
    logic [1:0]                  axi_mem_b_resp;
    logic [AXI_ID_WIDTH_S-1:0]   axi_mem_b_id;
    logic [AXI_USER_WIDTH-1:0]   axi_mem_b_user;
    logic                        axi_mem_b_ready;
    logic                        axi_mem_b_valid;

    assign axi_mem_aw_id     = axi_mem.aw_id;
    assign axi_mem_aw_addr   = axi_mem.aw_addr;
    assign axi_mem_aw_len    = axi_mem.aw_len;
    assign axi_mem_aw_size   = axi_mem.aw_size;
    assign axi_mem_aw_burst  = axi_mem.aw_burst;
    assign axi_mem_aw_lock   = axi_mem.aw_lock;
    assign axi_mem_aw_cache  = axi_mem.aw_cache;
    assign axi_mem_aw_prot   = axi_mem.aw_prot;
    assign axi_mem_aw_qos    = axi_mem.aw_qos;
    assign axi_mem_aw_region = axi_mem.aw_region;
    assign axi_mem_aw_user   = axi_mem.aw_user;
    assign axi_mem_aw_valid  = axi_mem.aw_valid;
    assign axi_mem_aw_ready  = axi_mem.aw_ready;
    assign axi_mem_w_last    = axi_mem.w_last;
    assign axi_mem_w_data    = axi_mem.w_data;
    assign axi_mem_w_strb    = axi_mem.w_strb;
    assign axi_mem_w_user    = axi_mem.w_user;
    assign axi_mem_w_valid   = axi_mem.w_valid;
    assign axi_mem_w_ready   = axi_mem.w_ready;
    assign axi_mem_b_id      = axi_mem.b_id;
    assign axi_mem_b_resp    = axi_mem.b_resp;
    assign axi_mem_b_user    = axi_mem.b_user;
    assign axi_mem_b_valid   = axi_mem.b_valid;
    assign axi_mem_b_ready   = axi_mem.b_ready;
    assign axi_mem_ar_id     = axi_mem.ar_id;
    assign axi_mem_ar_addr   = axi_mem.ar_addr;
    assign axi_mem_ar_len    = axi_mem.ar_len;
    assign axi_mem_ar_size   = axi_mem.ar_size;
    assign axi_mem_ar_burst  = axi_mem.ar_burst;
    assign axi_mem_ar_lock   = axi_mem.ar_lock;
    assign axi_mem_ar_cache  = axi_mem.ar_cache;
    assign axi_mem_ar_prot   = axi_mem.ar_prot;
    assign axi_mem_ar_qos    = axi_mem.ar_qos;
    assign axi_mem_ar_region = axi_mem.ar_region;
    assign axi_mem_ar_user   = axi_mem.ar_user;
    assign axi_mem_ar_valid  = axi_mem.ar_valid;
    assign axi_mem_ar_ready  = axi_mem.ar_ready;
    assign axi_mem_r_id      = axi_mem.r_id;
    assign axi_mem_r_last    = axi_mem.r_last;
    assign axi_mem_r_data    = axi_mem.r_data;
    assign axi_mem_r_resp    = axi_mem.r_resp;
    assign axi_mem_r_user    = axi_mem.r_user;
    assign axi_mem_r_valid   = axi_mem.r_valid;
    assign axi_mem_r_ready   = axi_mem.r_ready;

    Axi4PC #(
        .DATA_WIDTH   ( AXI_DATA_WIDTH ),
        .WID_WIDTH    ( AXI_ID_WIDTH_S ),
        .RID_WIDTH    ( AXI_ID_WIDTH_S ),
        .AWUSER_WIDTH ( AXI_USER_WIDTH ),
        .WUSER_WIDTH  ( AXI_USER_WIDTH ),
        .BUSER_WIDTH  ( AXI_USER_WIDTH ),
        .ARUSER_WIDTH ( AXI_USER_WIDTH ),
        .RUSER_WIDTH  ( AXI_USER_WIDTH ),
        .MAXRBURSTS   ( 32             ),
        .MAXWBURSTS   ( 32             ),
        .MAXWAITS     ( 64             ),
        .RecommendOn  ( 1'b1           ),
        .RecMaxWaitOn ( 1'b0           ),
        .ADDR_WIDTH   ( AXI_ADDR_WIDTH )
    ) i_axi4pc_mem (
        .ACLK     ( clk               ),
        .ARESETn  ( rst_n             ),
        .AWID     ( axi_mem_aw_id     ),
        .AWADDR   ( axi_mem_aw_addr   ),
        .AWLEN    ( axi_mem_aw_len    ),
        .AWSIZE   ( axi_mem_aw_size   ),
        .AWBURST  ( axi_mem_aw_burst  ),
        .AWLOCK   ( axi_mem_aw_lock   ),
        .AWCACHE  ( axi_mem_aw_cache  ),
        .AWPROT   ( axi_mem_aw_prot   ),
        .AWQOS    ( axi_mem_aw_qos    ),
        .AWREGION ( axi_mem_aw_region ),
        .AWUSER   ( axi_mem_aw_user   ),
        .AWVALID  ( axi_mem_aw_valid  ),
        .AWREADY  ( axi_mem_aw_ready  ),
        .WLAST    ( axi_mem_w_last    ),
        .WDATA    ( axi_mem_w_data    ),
        .WSTRB    ( axi_mem_w_strb    ),
        .WUSER    ( axi_mem_w_user    ),
        .WVALID   ( axi_mem_w_valid   ),
        .WREADY   ( axi_mem_w_ready   ),
        .BID      ( axi_mem_b_id      ),
        .BRESP    ( axi_mem_b_resp    ),
        .BUSER    ( axi_mem_b_user    ),
        .BVALID   ( axi_mem_b_valid   ),
        .BREADY   ( axi_mem_b_ready   ),
        .ARID     ( axi_mem_ar_id     ),
        .ARADDR   ( axi_mem_ar_addr   ),
        .ARLEN    ( axi_mem_ar_len    ),
        .ARSIZE   ( axi_mem_ar_size   ),
        .ARBURST  ( axi_mem_ar_burst  ),
        .ARLOCK   ( axi_mem_ar_lock   ),
        .ARCACHE  ( axi_mem_ar_cache  ),
        .ARPROT   ( axi_mem_ar_prot   ),
        .ARQOS    ( axi_mem_ar_qos    ),
        .ARREGION ( axi_mem_ar_region ),
        .ARUSER   ( axi_mem_ar_user   ),
        .ARVALID  ( axi_mem_ar_valid  ),
        .ARREADY  ( axi_mem_ar_ready  ),
        .RID      ( axi_mem_r_id      ),
        .RLAST    ( axi_mem_r_last    ),
        .RDATA    ( axi_mem_r_data    ),
        .RRESP    ( axi_mem_r_resp    ),
        .RUSER    ( axi_mem_r_user    ),
        .RVALID   ( axi_mem_r_valid   ),
        .RREADY   ( axi_mem_r_ready   ),
        .CACTIVE  ( '1                ),
        .CSYSREQ  ( '1                ),
        .CSYSACK  ( '1                )
    );

endmodule
