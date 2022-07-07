module axi4_mst_bfm #(
    parameter int AXI_DATA_WIDTH = 32           ,
    parameter int AXI_ADDR_WIDTH = 32           ,
    parameter int BACKPRESSURE_PROBABILITY = 0  ,
    parameter int MAX_BURST_LENGTH = 1          
)(
    input  bit                          clk_a           ,
    input  bit                          arstz_aq        ,
    
    // axi4 master
    output bit   [AXI_ADDR_WIDTH-1:0]   axi4_m_araddr   ,
    output bit   [1:0]                  axi4_m_arburst  ,
    output bit   [3:0]                  axi4_m_arcache  ,
    output bit   [7:0]                  axi4_m_arlen    ,
    output bit   [0:0]                  axi4_m_arlock   ,
    output bit   [2:0]                  axi4_m_arprot   ,
    output bit   [3:0]                  axi4_m_arqos    ,
    input  bit                          axi4_m_arready  ,
    output bit   [3:0]                  axi4_m_arregion ,
    output bit   [2:0]                  axi4_m_arsize   ,
    output bit                          axi4_m_arvalid  ,
    
    output bit   [AXI_ADDR_WIDTH-1:0]   axi4_m_awaddr   ,
    output bit   [1:0]                  axi4_m_awburst  ,
    output bit   [3:0]                  axi4_m_awcache  ,
    output bit   [7:0]                  axi4_m_awlen    ,
    output bit   [0:0]                  axi4_m_awlock   ,
    output bit   [2:0]                  axi4_m_awprot   ,
    output bit   [3:0]                  axi4_m_awqos    ,
    input  bit                          axi4_m_awready  ,
    output bit   [3:0]                  axi4_m_awregion ,
    output bit   [2:0]                  axi4_m_awsize   ,
    output bit                          axi4_m_awvalid  ,
    
    output bit                          axi4_m_bready   ,
    input  bit   [1:0]                  axi4_m_bresp    ,
    input  bit                          axi4_m_bvalid   ,
    
    input  bit   [AXI_DATA_WIDTH-1:0]   axi4_m_rdata    ,
    input  bit                          axi4_m_rlast    ,
    output bit                          axi4_m_rready   ,
    input  bit   [1:0]                  axi4_m_rresp    ,
    input  bit                          axi4_m_rvalid   ,
    
    output bit   [AXI_DATA_WIDTH-1:0]   axi4_m_wdata    ,
    output bit                          axi4_m_wlast    ,
    input  bit                          axi4_m_wready   ,
    output bit   [AXI_DATA_WIDTH/8-1:0] axi4_m_wstrb    ,
    output bit                          axi4_m_wvalid   
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
    int bresp_pending;
  
    ar_t ar_queue[$];
    ar_t ar_queue_in;
    ar_t ar_queue_out;

    r_t r_queue[$];
    r_t r_queue_in;
    r_t r_queue_out;
 
    bit tog;
    always @(posedge clk_a or negedge clk_a or negedge arstz_aq) begin
        if(!arstz_aq) begin
            tog <= '0;
        end
        else begin
            tog <= ~tog;
        end
    end

    always @ (posedge clk_a or negedge arstz_aq) begin
        if(~arstz_aq) begin
            axi4_m_bready  <= 0;
            axi4_m_rready  <= 0;
        end
        else begin
            axi4_m_bready  <= (({$random}%100) < BACKPRESSURE_PROBABILITY)? 0 : 1;
            axi4_m_rready  <= (({$random}%100) < BACKPRESSURE_PROBABILITY)? 0 : 1;
        end
    end
 
     // Write Address Channel
    always @ (posedge clk_a or negedge arstz_aq) begin
        if(~arstz_aq) begin
            axi4_m_awaddr   <= 0;
            axi4_m_awburst  <= 0;
            axi4_m_awcache  <= 0;
            axi4_m_awlen    <= 0;
            axi4_m_awlock   <= 0;
            axi4_m_awprot   <= 0;
            axi4_m_awqos    <= 0;
            axi4_m_awregion <= 0;
            axi4_m_awsize   <= 0;
            axi4_m_awvalid  <= 0;
        end
        else if(axi4_m_awvalid && !axi4_m_awready) begin
            // stall
        end
        else if((({$random}%100) < BACKPRESSURE_PROBABILITY) || aw_queue.size() == 0) begin
            axi4_m_awvalid  <= 0;
        end
        else begin
            aw_queue_out = aw_queue.pop_front();
            axi4_m_awaddr   <= aw_queue_out.awaddr;
            axi4_m_awburst  <= aw_queue_out.awburst;
            axi4_m_awcache  <= aw_queue_out.awcache;
            axi4_m_awlen    <= aw_queue_out.awlen;
            axi4_m_awlock   <= aw_queue_out.awlock;
            axi4_m_awprot   <= aw_queue_out.awprot;
            axi4_m_awqos    <= aw_queue_out.awqos;
            axi4_m_awregion <= aw_queue_out.awregion;
            axi4_m_awsize   <= aw_queue_out.awsize;
            axi4_m_awvalid  <= 1;
        end
    end
 
    // Write Data Channel
    always @ (posedge clk_a or negedge arstz_aq) begin
        if(~arstz_aq) begin
            axi4_m_wdata   <= 0;
            axi4_m_wlast   <= 0;
            axi4_m_wstrb   <= 0;
            axi4_m_wvalid  <= 0;  
        end
        else if(axi4_m_wvalid && !axi4_m_wready) begin
            // stall
        end
        else if((({$random}%100) < BACKPRESSURE_PROBABILITY) || w_queue.size() == 0) begin
            axi4_m_wvalid  <= 0;
        end
        else begin
            w_queue_out = w_queue.pop_front();
            axi4_m_wdata <= w_queue_out.wdata;
            axi4_m_wlast <= w_queue_out.wlast;
            axi4_m_wstrb <= w_queue_out.wstrb;
            axi4_m_wvalid <= 1;
        end
    end    
 
    // Write Response Channel
    always @ (posedge clk_a) begin
        if(axi4_m_bready && axi4_m_bvalid) begin
            b_queue_in.bresp = axi4_m_bresp;
            b_queue.push_back(b_queue_in);
        end
    end

    initial bresp_pending = 0;

    // Read Address Channel
    always @ (posedge clk_a or negedge arstz_aq) begin
        if(~arstz_aq) begin
            axi4_m_araddr  <= 0;
            axi4_m_arburst <= 0;
            axi4_m_arcache <= 0;
            axi4_m_arlen   <= 0;
            axi4_m_arlock  <= 0;
            axi4_m_arprot  <= 0;
            axi4_m_arqos   <= 0;
            axi4_m_arregion<= 0;
            axi4_m_arsize  <= 0;
            axi4_m_arvalid <= 0;
        end
        else if(axi4_m_arvalid && !axi4_m_arready) begin
            // stall
        end
        else if((({$random}%100) < BACKPRESSURE_PROBABILITY) || ar_queue.size() == 0) begin
            axi4_m_arvalid <= 0;
        end
        else begin
            ar_queue_out = ar_queue.pop_front();
            axi4_m_araddr  <= ar_queue_out.araddr;
            axi4_m_arburst <= ar_queue_out.arburst;
            axi4_m_arcache <= ar_queue_out.arcache;
            axi4_m_arlen   <= ar_queue_out.arlen;
            axi4_m_arlock  <= ar_queue_out.arlock;
            axi4_m_arprot  <= ar_queue_out.arprot;
            axi4_m_arqos   <= ar_queue_out.arqos;
            axi4_m_arregion<= ar_queue_out.arregion;
            axi4_m_arsize  <= ar_queue_out.arsize;
            axi4_m_arvalid <= 1;
        end
    end

    // Read Response Channel
    always @ (posedge clk_a) begin
        if(axi4_m_rready && axi4_m_rvalid) begin
            r_queue_in.rdata = axi4_m_rdata;
            r_queue_in.rlast = axi4_m_rlast;
            r_queue_in.rresp = axi4_m_rresp;
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
    //        while(bresp_pending > max_pending) @ (posedge clk_a);
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
    //        while(bresp_pending != 0) @ (posedge clk_a);
    //    end
    //endtask

    // Write response
    always @(posedge clk_a) begin // write response channel
        while((b_queue.size() == 0) || !tog) begin end
        b_queue_out = b_queue.pop_front();

        if (b_queue_out.bresp != 2'b0) begin
            $display("*ERROR:BRESP Error detected while writing");
            //$stop;
        end

        bresp_pending = bresp_pending - 1;
        assert(bresp_pending >= 0);
    end

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

    //// task read32
    //// Reads one 32bit word
    //task read32 (input int address, output int data);
    //    begin
    //        // wait until all posted writes have completed
    //while(bresp_pending != 0) @ (posedge clk_a);
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
    //        while(r_queue.size() == 0) @ (posedge clk_a);
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
    //        while(bresp_pending != 0) @ (posedge clk_a);
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
    //                        while(r_queue.size() == 0) @ (posedge clk_a);
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

