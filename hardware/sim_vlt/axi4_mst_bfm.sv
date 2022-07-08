module axi4_mst_bfm #(
    parameter int AXI_DATA_WIDTH = 32           ,
    parameter int AXI_ADDR_WIDTH = 32           ,
    parameter int BACKPRESSURE_PROBABILITY = 0  ,
    parameter int MAX_BURST_LENGTH = 1          
) (
    input  bit                          clk         ,
    input  bit                          resetn      ,
    
    // axi4 master
    output bit   [AXI_ADDR_WIDTH-1:0]   araddr      ,
    output bit   [1:0]                  arburst     ,
    output bit   [3:0]                  arcache     ,
    output bit   [7:0]                  arlen       ,
    output bit   [0:0]                  arlock      ,
    output bit   [2:0]                  arprot      ,
    output bit   [3:0]                  arqos       ,
    input  bit                          arready     ,
    output bit   [3:0]                  arregion    ,
    output bit   [2:0]                  arsize      ,
    output bit                          arvalid     ,
    
    output bit   [AXI_ADDR_WIDTH-1:0]   awaddr      ,
    output bit   [1:0]                  awburst     ,
    output bit   [3:0]                  awcache     ,
    output bit   [7:0]                  awlen       ,
    output bit   [0:0]                  awlock      ,
    output bit   [2:0]                  awprot      ,
    output bit   [3:0]                  awqos       ,
    input  bit                          awready     ,
    output bit   [3:0]                  awregion    ,
    output bit   [2:0]                  awsize      ,
    output bit                          awvalid     ,
    
    output bit                          bready      ,
    input  bit   [1:0]                  bresp       ,
    input  bit                          bvalid      ,
    
    input  bit   [AXI_DATA_WIDTH-1:0]   rdata       ,
    input  bit                          rlast       ,
    output bit                          rready      ,
    input  bit   [1:0]                  rresp       ,
    input  bit                          rvalid      ,
    
    output bit   [AXI_DATA_WIDTH-1:0]   wdata       ,
    output bit                          wlast       ,
    input  bit                          wready      ,
    output bit   [AXI_DATA_WIDTH/8-1:0] wstrb       ,
    output bit                          wvalid      
);

    typedef struct packed {
        bit [AXI_ADDR_WIDTH-1:0] awaddr;
        bit [1:0]  awburst;
        bit [3:0]  awcache;
        bit [7:0]  awlen;
        bit [0:0]  awlock;
        bit [2:0]  awprot;
        bit [3:0]  awqos;
        bit [3:0]  awregion;
        bit [2:0]  awsize;
    } aw_t;

    typedef struct packed {
        bit [AXI_DATA_WIDTH-1:0]  wdata;
        bit        wlast;
        bit [AXI_DATA_WIDTH/8-1:0] wstrb;
    } w_t;

    typedef struct packed {
        bit [1:0]  bresp;
    } b_t;

    typedef struct packed {
        bit [AXI_ADDR_WIDTH-1:0] araddr;
        bit [1:0]  arburst;
        bit [3:0]  arcache;
        bit [7:0]  arlen;
        bit [0:0]  arlock;
        bit [2:0]  arprot;
        bit [3:0]  arqos;
        bit [3:0]  arregion;
        bit [2:0]  arsize;
    } ar_t;
 
    typedef struct packed {
        bit [AXI_DATA_WIDTH-1:0]rdata;
        bit        rlast;
        bit [1:0]  rresp;
    } r_t;

    aw_t aw_queue[$];
    aw_t aw_queue_in;
    aw_t aw_queue_out;

    w_t w_queue[$];
    w_t w_queue_in;
    w_t w_queue_out;

    b_t b_queue[$];
    b_t b_queue_in;
    b_t b_queue_out;
    int bresp_pending = '0;
  
    ar_t ar_queue[$];
    ar_t ar_queue_in;
    ar_t ar_queue_out;

    r_t r_queue[$];
    r_t r_queue_in;
    r_t r_queue_out;
 
    bit tog; // for verilator, to remove @-wait event
    always_ff @(posedge clk or negedge clk or negedge resetn) begin
        if(!resetn) begin
            tog <= 0;
        end
        else begin
            tog <= ~tog;
        end
    end

    always_ff @ (posedge clk or negedge resetn) begin
        if(~resetn) begin
            bready  <= 0;
            rready  <= 0;
        end
        else begin
            bready  <= (({$random}%100) < BACKPRESSURE_PROBABILITY)? 0 : 1;
            rready  <= (({$random}%100) < BACKPRESSURE_PROBABILITY)? 0 : 1;
        end
    end
 
    // Write Address Channel
    assign  awaddr   = aw_queue_out.awaddr      ;
    assign  awburst  = aw_queue_out.awburst     ;
    assign  awcache  = aw_queue_out.awcache     ;
    assign  awlen    = aw_queue_out.awlen       ;
    assign  awlock   = aw_queue_out.awlock      ;
    assign  awprot   = aw_queue_out.awprot      ;
    assign  awqos    = aw_queue_out.awqos       ;
    assign  awregion = aw_queue_out.awregion    ;
    assign  awsize   = aw_queue_out.awsize      ;

    always_ff @(posedge clk or negedge resetn) begin
        if(~resetn) begin
            aw_queue_out <= '0;
            awvalid  <= 0;
        end
        else if(awvalid && !awready) begin
            // stall
        end
        else if((({$random}%100) < BACKPRESSURE_PROBABILITY) || aw_queue.size() == 0) begin
            awvalid  <= 0;
        end
        else begin
            aw_queue_out = aw_queue.pop_front(); // TODO
            awvalid  <= 1;
        end
    end
 
    // Write Data Channel
    assign  wdata = w_queue_out.wdata;
    assign  wlast = w_queue_out.wlast;
    assign  wstrb = w_queue_out.wstrb;

    always_ff @(posedge clk or negedge resetn) begin
        if(~resetn) begin
            w_queue_out <= '0;
            wvalid  <= 0;  
        end
        else if(wvalid && !wready) begin
            // stall
        end
        else if((({$random}%100) < BACKPRESSURE_PROBABILITY) || w_queue.size() == 0) begin
            wvalid  <= 0;
        end
        else begin
            w_queue_out = w_queue.pop_front(); // TODO
            wvalid <= 1;
        end
    end    
 
    // Write Response Channel
    assign  b_queue_in.bresp = bresp;

    always_ff @(posedge clk) begin
        if(bready && bvalid) begin
            b_queue.push_back(b_queue_in);
        end
    end

    always_ff @(posedge clk) begin
        if(b_queue.size() != 0) begin
            b_queue_out = b_queue.pop_front(); // TODO

            if (b_queue_out.bresp != 2'b0) begin
                $display("*ERROR:BRESP Error detected while writing");
                //$stop;
            end

            bresp_pending <= bresp_pending - 1;
        end
        //assert(bresp_pending >= 0);
    end


    // Read Address Channel
    assign  araddr   = ar_queue_out.araddr;
    assign  arburst  = ar_queue_out.arburst;
    assign  arcache  = ar_queue_out.arcache;
    assign  arlen    = ar_queue_out.arlen;
    assign  arlock   = ar_queue_out.arlock;
    assign  arprot   = ar_queue_out.arprot;
    assign  arqos    = ar_queue_out.arqos;
    assign  arregion = ar_queue_out.arregion;
    assign  arsize   = ar_queue_out.arsize;

    always_ff @(posedge clk or negedge resetn) begin
        if(~resetn) begin
            ar_queue_out <= '0;
            arvalid <= 0;
        end
        else if(arvalid && !arready) begin
            // stall
        end
        else if((({$random}%100) < BACKPRESSURE_PROBABILITY) || ar_queue.size() == 0) begin
            arvalid <= 0;
        end
        else begin
            ar_queue_out = ar_queue.pop_front();
            arvalid <= 1;
        end
    end

    // Read Response Channel
    assign  r_queue_in.rdata = rdata;
    assign  r_queue_in.rlast = rlast;
    assign  r_queue_in.rresp = rresp;

    always_ff @(posedge clk) begin
        if(rready && rvalid) begin
            r_queue.push_back(r_queue_in);
        end
    end   


    //------------------------------------------------------------------------------
    // TASK API
    //------------------------------------------------------------------------------
    byte block_buf[];
    integer aw_remaining_beats;
    integer w_remaining_beats;
    integer w_burst_size;
    integer ar_remaining_beats;
    integer r_remaining_beats;
    integer r_burst_size;

    task write32 (input int address, input int data, input int max_pending = 0);
        begin
            aw_queue_in.awaddr  = address;
            aw_queue_in.awburst = 0;
            aw_queue_in.awcache = 0;
            aw_queue_in.awlen   = 0;
            aw_queue_in.awlock  = 0;
            aw_queue_in.awprot  = 0;
            aw_queue_in.awqos   = 0;
            aw_queue_in.awregion= 0;
            aw_queue_in.awsize  = 2; // 4bytes

            aw_queue.push_back(aw_queue_in);

            bresp_pending = bresp_pending + 1;
            
            if(AXI_DATA_WIDTH == 32) begin
                w_queue_in.wdata = data;
                w_queue_in.wstrb = 4'hf;
            end
            else if(AXI_DATA_WIDTH == 64) begin
                w_queue_in.wdata = {2{data}};
                w_queue_in.wstrb = 8'h0f << (address[2]*4);
            end
            else if(AXI_DATA_WIDTH == 128) begin
                w_queue_in.wdata = {4{data}};
                w_queue_in.wstrb = 16'h000f << (address[3:2]*4);
            end
            else if(AXI_DATA_WIDTH == 256) begin
                w_queue_in.wdata = {8{data}};
                w_queue_in.wstrb = 32'h0000000f << (address[4:2]*4);
            end
            w_queue_in.wlast = 1;

            w_queue.push_back(w_queue_in);
            
            // wait until all posted writes have completed
            while((bresp_pending > max_pending) || !tog) begin end
        end
    endtask

    task read32 (input int address, output int data);
        begin
            // wait until all posted writes have completed
            while((bresp_pending != 0) || !tog);
                
            ar_queue_in.araddr  = address;
            ar_queue_in.arburst = 0;
            ar_queue_in.arcache = 0;
            ar_queue_in.arlen   = 0;
            ar_queue_in.arlock  = 0;
            ar_queue_in.arprot  = 0;
            ar_queue_in.arqos   = 0;
            ar_queue_in.arregion= 0;
            ar_queue_in.arsize  = 2; // 4bytes

            ar_queue.push_back(ar_queue_in);
                
            while((r_queue.size() == 0) || !tog) begin end
            r_queue_out = r_queue.pop_front();
            if(AXI_DATA_WIDTH == 32)
                data = r_queue_out.rdata;
            else if(AXI_DATA_WIDTH == 64)
                data = r_queue_out.rdata >> (address[2]*32);
            else if(AXI_DATA_WIDTH == 128)
                data = r_queue_out.rdata >> (address[3:2]*32);
            else if(AXI_DATA_WIDTH == 256)
                data = r_queue_out.rdata >> (address[4:2]*32);

            if (r_queue_out.rresp != 2'b0) begin
                $display("*ERROR:RRESP Error detected while writing");
                //$stop;
            end
        end
    endtask

    //// task write32
    //// Writes one 32bit word
    //// Blocks until response is received from final destination
    //task write32 (input int address, input int data, input int max_pending = 0);
    //    begin
    //        fork
    //            // Job 1: write address channel 
    //            begin
    //                aw_queue_in.awaddr  = address;
    //                aw_queue_in.awburst = 0;
    //                aw_queue_in.awcache = 0;
    //                aw_queue_in.awlen   = 0;
    //                aw_queue_in.awlock  = 0;
    //                aw_queue_in.awprot  = 0;
    //                aw_queue_in.awqos   = 0;
    //                aw_queue_in.awregion= 0;
    //                aw_queue_in.awsize  = 2; // 4bytes

    //                aw_queue.push_back(aw_queue_in);

    //                bresp_pending = bresp_pending + 1;
    //            end
    //            // Job 2: write data channel
    //            begin
    //                if(AXI_DATA_WIDTH == 32) begin
    //                    w_queue_in.wdata = data;
    //                    w_queue_in.wstrb = 4'hf;
    //                end
    //                else if(AXI_DATA_WIDTH == 64) begin
    //                    w_queue_in.wdata = {2{data}};
    //                    w_queue_in.wstrb = 8'h0f << (address[2]*4);
    //                end
    //                else if(AXI_DATA_WIDTH == 128) begin
    //                    w_queue_in.wdata = {4{data}};
    //                    w_queue_in.wstrb = 16'h000f << (address[3:2]*4);
    //                end
    //                else if(AXI_DATA_WIDTH == 256) begin
    //                    w_queue_in.wdata = {8{data}};
    //                    w_queue_in.wstrb = 32'h0000000f << (address[4:2]*4);
    //                end
    //                w_queue_in.wlast = 1;

    //                w_queue.push_back(w_queue_in);
    //            end
    //        join
    //        // wait until all posted writes have completed
    //        while(bresp_pending > max_pending) @ (posedge clk);
    //    end
    //endtask


    //task write_block (input int address, input int size);
    //    begin
    //        assert((address % (AXI_DATA_WIDTH/8)) == 0) else $stop;  //aligned address
    //        assert((size    % (AXI_DATA_WIDTH/8)) == 0) else $stop;  //aligned size
    //        aw_remaining_beats = size / (AXI_DATA_WIDTH/8);
    //        w_remaining_beats  = size / (AXI_DATA_WIDTH/8);

    //        fork
    //            // Job 1: make write address request.
    //            begin
    //                for(int i=0; i<size; i=i+(AXI_DATA_WIDTH/8)*MAX_BURST_LENGTH) begin
    //                    aw_queue_in.awaddr  = address + i;
    //                    aw_queue_in.awburst = 1; // incrementing burst
    //                    aw_queue_in.awcache = 0;
    //                    aw_queue_in.awlen   = (aw_remaining_beats < MAX_BURST_LENGTH)
    //                                          ? aw_remaining_beats -1 
    //                                          : MAX_BURST_LENGTH - 1;
    //                    aw_queue_in.awlock  = 0;
    //                    aw_queue_in.awprot  = 0;
    //                    aw_queue_in.awqos   = 0;
    //                    aw_queue_in.awregion= 0;
    //                    aw_queue_in.awsize  = (AXI_DATA_WIDTH==32)  ? 2 : 
    //                                          (AXI_DATA_WIDTH==64)  ? 3 :
    //                                          (AXI_DATA_WIDTH==128) ? 4 : 
    //                                          (AXI_DATA_WIDTH==256) ? 5 : 0;

    //                    aw_queue.push_back(aw_queue_in);

    //                    aw_remaining_beats = aw_remaining_beats - MAX_BURST_LENGTH;
    //                    bresp_pending = bresp_pending + 1;
    //                end
    //            end

    //            // Job 2: make write data request.
    //            begin
    //                for(int i=0; i<size; i=i+(AXI_DATA_WIDTH/8)*MAX_BURST_LENGTH) begin
    //                    w_burst_size = (w_remaining_beats < MAX_BURST_LENGTH) 
    //                                   ? w_remaining_beats * (AXI_DATA_WIDTH/8) 
    //                                   : MAX_BURST_LENGTH * (AXI_DATA_WIDTH/8);

    //                    for(int j=0; j<w_burst_size; j=j+(AXI_DATA_WIDTH/8)) begin
    //                        for(int k=0; k<AXI_DATA_WIDTH/8; k++) begin
    //                            w_queue_in.wdata[k*8+:8] = block_buf[i+j+k];
    //                        end
    //                        w_queue_in.wstrb = {(AXI_DATA_WIDTH/8){1'b1}};
    //                        w_queue_in.wlast = (j+(AXI_DATA_WIDTH/8) == w_burst_size)? 1 : 0;
    //                        w_queue.push_back(w_queue_in);
    //                    end
    //                    w_remaining_beats = w_remaining_beats - MAX_BURST_LENGTH;
    //                end
    //            end
    //        join
    //        // wait until all posted writes have completed
    //        while(bresp_pending != 0) @ (posedge clk);
    //    end
    //endtask


    //// task read32
    //// Reads one 32bit word
    //task read32 (input int address, output int data);
    //    begin
    //        // wait until all posted writes have completed
    //while(bresp_pending != 0) @ (posedge clk);
    //        fork
    //            // Job 1: read address channel
    //            begin 
    //                ar_queue_in.araddr  = address;
    //                ar_queue_in.arburst = 0;
    //                ar_queue_in.arcache = 0;
    //                ar_queue_in.arlen   = 0;
    //                ar_queue_in.arlock  = 0;
    //                ar_queue_in.arprot  = 0;
    //                ar_queue_in.arqos   = 0;
    //                ar_queue_in.arregion= 0;
    //                ar_queue_in.arsize  = 2; // 4bytes

    //                ar_queue.push_back(ar_queue_in);
    //            end
    //            // Job 2: read response channel
    //            begin 
    //        while(r_queue.size() == 0) @ (posedge clk);
    //                r_queue_out = r_queue.pop_front();
    //                if(AXI_DATA_WIDTH == 32)
    //                    data = r_queue_out.rdata;
    //                else if(AXI_DATA_WIDTH == 64)
    //                    data = r_queue_out.rdata >> (address[2]*32);
    //                else if(AXI_DATA_WIDTH == 128)
    //                    data = r_queue_out.rdata >> (address[3:2]*32);
    //                else if(AXI_DATA_WIDTH == 256)
    //                    data = r_queue_out.rdata >> (address[4:2]*32);

    //                if (r_queue_out.rresp != 2'b0) begin
    //                    $display("*ERROR:RRESP Error detected while writing");
    //                    //$stop;
    //                end
    //            end
    //        join
    //    end
    //endtask

    //task read_block (input int address, input int size);
    //    begin
    //        assert((address % (AXI_DATA_WIDTH/8)) == 0) else $stop;  //aligned address
    //        assert((size    % (AXI_DATA_WIDTH/8)) == 0) else $stop;  //aligned size
    //        ar_remaining_beats = size / (AXI_DATA_WIDTH/8);
    //        r_remaining_beats  = size / (AXI_DATA_WIDTH/8);
    //        // wait until all posted writes have completed
    //        while(bresp_pending != 0) @ (posedge clk);
    //        fork
    //            begin
    //                for(int i=0; i<size; i=i+(AXI_DATA_WIDTH/8)*MAX_BURST_LENGTH) begin
    //                    ar_queue_in.araddr  = address + i;
    //                    ar_queue_in.arburst = 1; // incrementing burst
    //                    ar_queue_in.arcache = 0;
    //                    ar_queue_in.arlen   = (ar_remaining_beats < MAX_BURST_LENGTH)
    //                                          ? ar_remaining_beats -1 : MAX_BURST_LENGTH - 1;
    //                    ar_queue_in.arlock  = 0;
    //                    ar_queue_in.arprot  = 0;
    //                    ar_queue_in.arqos   = 0;
    //                    ar_queue_in.arregion= 0;
    //                    ar_queue_in.arsize  = (AXI_DATA_WIDTH==32)  ? 2 :
    //                                          (AXI_DATA_WIDTH==64)  ? 3 :
    //                                          (AXI_DATA_WIDTH==128) ? 4 : 
    //                                          (AXI_DATA_WIDTH==256) ? 5 : 0;

    //                    ar_queue.push_back(ar_queue_in);

    //                    ar_remaining_beats = ar_remaining_beats - MAX_BURST_LENGTH;
    //                end
    //            end
    //            begin
    //                for(int i=0; i<size; i=i+(AXI_DATA_WIDTH/8)*MAX_BURST_LENGTH) begin
    //                    r_burst_size = (r_remaining_beats < MAX_BURST_LENGTH)
    //                                   ? r_remaining_beats * (AXI_DATA_WIDTH/8) 
    //                                   : MAX_BURST_LENGTH * (AXI_DATA_WIDTH/8);

    //                    for(int j=0; j<r_burst_size; j=j+(AXI_DATA_WIDTH/8)) begin
    //                        while(r_queue.size() == 0) @ (posedge clk);
    //                        r_queue_out = r_queue.pop_front();
    //                        for(int k=0; k<AXI_DATA_WIDTH/8; k++) begin
    //                            block_buf[i+j+k] = r_queue_out.rdata[k*8+:8];
    //                        end
    //                    end
    //                    r_remaining_beats = r_remaining_beats - MAX_BURST_LENGTH;
    //                end
    //            end
    //        join
    //    end
    //endtask


endmodule

