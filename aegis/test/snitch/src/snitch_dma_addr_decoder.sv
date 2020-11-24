// Snitch DMA address decoder
// groups a number of banks in the TCDM to superbanks. One superbank can be served by the DMA
// in one cycle.

/// Author: Thomas Benz <tbenz@ethz.ch>

module snitch_dma_addr_decoder #(
  parameter int unsigned TCDMAddrWidth     = -1,
  parameter int unsigned DMAAddrWidth      = -1,
  parameter int unsigned BanksPerSuperbank = -1,
  parameter int unsigned NrSuperBanks      = -1,
  parameter int unsigned DMADataWidth      = -1,
  parameter int unsigned MemoryLatency     = -1
) (

  input   logic                                           clk_i,
  input   logic                                           rst_i,

  // single port towards dma
  input   logic                                           dma_req_i,          // Bank request
  output  logic                                           dma_gnt_o,          // Bank grant
  input   logic                   [DMAAddrWidth-1:0   ]   dma_add_i,          // Address
  input   logic                   [3:0                ]   dma_amo_i,          // Atomic Memory Operation
  input   logic                                           dma_wen_i,          // 1: Store, 0: Load
  input   logic                   [DMADataWidth-1:0   ]   dma_wdata_i,        // Write data
  input   logic                   [DMADataWidth/8-1:0 ]   dma_be_i,           // Byte enable
  output  logic                   [DMADataWidth-1:0   ]   dma_rdata_o,        // Read data

    // dma side
  output  logic [NrSuperBanks-1:0]                        super_bank_req_o,   // Bank request
  input   logic [NrSuperBanks-1:0]                        super_bank_gnt_i,   // Bank grant
  output  logic [NrSuperBanks-1:0][TCDMAddrWidth-1:0  ]   super_bank_add_o,   // Address
  output  logic [NrSuperBanks-1:0][3:0                ]   super_bank_amo_o,   // Atomic Memory Operation
  output  logic [NrSuperBanks-1:0]                        super_bank_wen_o,   // 1: Store, 0: Load
  output  logic [NrSuperBanks-1:0][DMADataWidth-1:0   ]   super_bank_wdata_o, // Write data
  output  logic [NrSuperBanks-1:0][DMADataWidth/8-1:0 ]   super_bank_be_o,    // Byte enable
  input   logic [NrSuperBanks-1:0][DMADataWidth-1:0   ]   super_bank_rdata_i  // Read data
);

  localparam SBWidth           = $clog2(NrSuperBanks);
  localparam DMADataWidthBytes = DMADataWidth / 8;
  localparam NumBitsDMATrans   = $clog2(DMADataWidthBytes); // example case: 6

  // case for 512 bits, 32 banks, 4 superbanks, 1024 words per bank, 256kiB, 64bit system
  // 31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 09 08 07 06 05 04 03 02 01 00
  // 00000000000000000000000000000000000000000|-----------------------------|-----|--------|--------|
  // zero or ignored                            tcdm line address            superbank      byte in bank
  //                                                                               subbank

  localparam TCDMUpper = SBWidth + NumBitsDMATrans + TCDMAddrWidth;

  // super bank address
  logic [SBWidth-1:0]                    super_bank;
  logic [TCDMAddrWidth-1:0]              tcdm_line_address;
  // have to keep the last choosen bank to correctly route response (rdata back)
  // the memory can have a parametrizable amount of delay.
  logic [MemoryLatency-1:0][SBWidth-1:0] super_bank_q;

  // divide the address
  assign super_bank        = dma_add_i[SBWidth+NumBitsDMATrans-1:NumBitsDMATrans];
  assign tcdm_line_address = dma_add_i[TCDMUpper-1:TCDMUpper-TCDMAddrWidth];


  // create the mux inthe forward and backwords direction
  always_comb begin : proc_dma_addr_decoder

    // unused ports are set to 0
    super_bank_req_o   = '0;
    super_bank_add_o   = '0;
    super_bank_amo_o   = '0;
    super_bank_wen_o   = '0;
    super_bank_wdata_o = '0;
    super_bank_be_o    = '0;

    // mux
    super_bank_req_o   [super_bank] = dma_req_i;
    super_bank_add_o   [super_bank] = tcdm_line_address;
    super_bank_amo_o   [super_bank] = dma_amo_i;
    super_bank_wen_o   [super_bank] = dma_wen_i;
    super_bank_wdata_o [super_bank] = dma_wdata_i;
    super_bank_be_o    [super_bank] = dma_be_i;

    dma_gnt_o                       = super_bank_gnt_i   [super_bank];

    // backwards path has be delayed by one, as memory has one cycle latency
    dma_rdata_o                     = super_bank_rdata_i [super_bank_q[MemoryLatency-1]];

  end

  always_ff @(posedge clk_i) begin : proc_delay_bank_choice
    if (rst_i) begin
       super_bank_q<= 0;
    end else begin
      super_bank_q[0] <= super_bank;
      // implement the shift for the delay
      if (MemoryLatency > 1) begin
        for (int i = 1; i < MemoryLatency; i++) begin
          super_bank_q[i] <= super_bank_q[i-1];
        end
      end
    end
  end

endmodule : snitch_dma_addr_decoder
