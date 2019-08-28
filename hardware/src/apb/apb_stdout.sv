module apb_stdout #(
  parameter int unsigned  N_CORES     = 0,
  parameter int unsigned  N_CLUSTERS  = 0,
  parameter int unsigned  ADDR_WIDTH  = 0,
  parameter int unsigned  DATA_WIDTH  = 0
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  APB_BUS.Slave apb
);

  byte buffer [N_CLUSTERS-1:0][N_CORES-1:0][$];

  function void flush(int unsigned i_cl, int unsigned i_core);
    automatic string s;
    for (int i_char = 0; i_char < buffer[i_cl][i_core].size(); i_char++) begin
      s = $sformatf("%s%c", s, buffer[i_cl][i_core][i_char]);
    end
    if (s.len() > 0) begin
      $display("[%01d,%01d] %s", i_cl, i_core, s);
    end
    buffer[i_cl][i_core] = {};
  endfunction

  function void append(int unsigned i_cl, int unsigned i_core, byte ch);
    if (ch == 8'hA) begin
      flush(i_cl, i_core);
    end else begin
      buffer[i_cl][i_core].push_back(ch);
    end
  endfunction

  always_ff @(posedge clk_i or negedge rst_ni) begin
    int unsigned cl_idx, core_idx;
    byte data;
    if (!rst_ni) begin
      for (int i_cl = 0; i_cl < N_CLUSTERS; i_cl++) begin
        for (int i_core = 0; i_core < N_CORES; i_core++) begin
          flush(i_cl, i_core);
        end
      end
    end else begin
      if (apb.psel && apb.penable && apb.pwrite) begin
        cl_idx = (apb.paddr >> 7) & 32'hF;
        core_idx = (apb.paddr >> 3) & 32'hF;
        if (cl_idx < N_CLUSTERS && core_idx < N_CORES) begin
          data = apb.pwdata & 32'hFF;
          append(cl_idx, core_idx, data);
        end
      end
    end
  end

  assign apb.prdata = '0;
  assign apb.pslverr = 1'b0;
  assign apb.pready = 1'b1;

endmodule
