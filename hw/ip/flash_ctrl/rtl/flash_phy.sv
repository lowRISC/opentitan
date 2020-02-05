// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Module
//
//
// This module is an early attempt to model what a custom phy module might look like
// Long term, it is expected this module will split into its own entity under hw/ip
// with its own set of register that support technology / node specific flash settings
// More of those details will be worked out with future partner engagement

module flash_phy #(
  parameter int NumBanks = 2,
  parameter int PagesPerBank = 256, // pages per bank
  parameter int WordsPerPage = 256, // words per page
  parameter int DataWidth   = 32, // bits per word

  //Do not touch - Derived parameters
  localparam int BankW = $clog2(NumBanks),
  localparam int PageW = $clog2(PagesPerBank),
  localparam int WordW = $clog2(WordsPerPage),
  localparam int AddrW = BankW + PageW + WordW
) (
  input clk_i,
  input rst_ni,
  input host_req_i,
  input [AddrW-1:0] host_addr_i,
  output logic host_req_rdy_o,
  output logic host_req_done_o,
  output logic [DataWidth-1:0] host_rdata_o,
  input flash_ctrl_pkg::flash_req_t flash_ctrl_i,
  output flash_ctrl_pkg::flash_rsp_t flash_ctrl_o
);

  // Flash macro outstanding refers to how many reads we allow a macro to move ahead of an
  // in order blocking read. Since the data cannot be returned out of order, this simply
  // does the reads in advance and store them in a FIFO
  localparam int FlashMacroOustanding = 1;
  localparam int SeqFifoDepth = FlashMacroOustanding * NumBanks;

  // flash_phy forwards incoming host transactions to the appropriate bank but is not aware of
  // any controller / host arbitration within the bank.  This means it is possible for
  // flash_phy to forward one transaction to bank N and another to bank N+1 only for bank N+1
  // to finish its transaction first (if for example a controller operation were ongoing in bank
  // N).
  // This implies that even though transactions are received in-order, they can complete out of
  // order.  Thus it is the responsibility of the flash_phy to sequence the responses correctly.
  // For banks that have finished ahead of time, it is also important to hold its output until
  // consumed.

  // host to flash_phy interface
  logic [BankW-1:0]     host_bank_sel;
  logic [BankW-1:0]     rsp_bank_sel;
  logic [NumBanks-1:0]  host_req_rdy;
  logic [NumBanks-1:0]  host_req_done;
  logic [NumBanks-1:0]  host_rsp_avail;
  logic [NumBanks-1:0]  host_rsp_vld;
  logic [NumBanks-1:0]  host_rsp_ack;
  logic [DataWidth-1:0] host_rsp_data [NumBanks];
  logic                 seq_fifo_rdy;
  logic                 seq_fifo_pending;


  // flash_ctrl to flash_phy interface
  logic [BankW-1:0]     ctrl_bank_sel;
  logic [NumBanks-1:0]  rd_done;
  logic [NumBanks-1:0]  prog_done;
  logic [NumBanks-1:0]  erase_done;
  logic [NumBanks-1:0]  init_busy;

  // common interface
  logic [DataWidth-1:0] rd_data [NumBanks];

  // select which bank each is operating on
  assign host_bank_sel = host_req_i ? host_addr_i[PageW + WordW +: BankW] : '0;
  assign ctrl_bank_sel = flash_ctrl_i.addr[PageW + WordW +: BankW];

  // accept transaction if bank is ready and previous response NOT pending
  assign host_req_rdy_o = host_req_rdy[host_bank_sel] & host_rsp_avail[host_bank_sel] &
                          seq_fifo_rdy;

  assign host_req_done_o = seq_fifo_pending & host_rsp_vld[rsp_bank_sel];
  assign host_rdata_o = host_rsp_data[rsp_bank_sel];

  assign flash_ctrl_o.rd_done = rd_done[ctrl_bank_sel];
  assign flash_ctrl_o.prog_done = prog_done[ctrl_bank_sel];
  assign flash_ctrl_o.erase_done = erase_done[ctrl_bank_sel];
  assign flash_ctrl_o.rd_data = rd_data[ctrl_bank_sel];
  assign flash_ctrl_o.init_busy = |init_busy;

  // This fifo holds the expected return order
  prim_fifo_sync #(
      .Width  (BankW),
      .Pass   (0),
      .Depth  (SeqFifoDepth)
    ) bank_sequence_fifo (
      .clk_i,
      .rst_ni,
      .clr_i  (1'b0),
      .wvalid (host_req_i & host_req_rdy_o),
      .wready (seq_fifo_rdy),
      .wdata  (host_bank_sel),
      .depth  (),
      .rvalid (seq_fifo_pending),
      .rready (host_req_done_o),
      .rdata  (rsp_bank_sel)
    );

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_flash_banks

    // pop if the response came from the appropriate fifo
    assign host_rsp_ack[bank] = host_req_done_o & (rsp_bank_sel == bank);

    prim_fifo_sync #(
      .Width  (DataWidth),
      .Pass   (1'b1),
      .Depth  (FlashMacroOustanding)
    ) host_rsp_fifo (
      .clk_i,
      .rst_ni,
      .clr_i  (1'b0),
      .wvalid (host_req_done[bank]),
      .wready (host_rsp_avail[bank]),
      .wdata  (rd_data[bank]),
      .depth  (),
      .rvalid (host_rsp_vld[bank]),
      .rready (host_rsp_ack[bank]),
      .rdata  (host_rsp_data[bank])
    );

    prim_flash #(
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth)
    ) u_flash (
      .clk_i,
      .rst_ni,
      .req_i(flash_ctrl_i.req & (ctrl_bank_sel == bank)),
      .host_req_i(host_req_i & host_req_rdy_o & (host_bank_sel == bank)),
      .host_addr_i(host_addr_i[0 +: PageW + WordW]),
      .rd_i(flash_ctrl_i.rd),
      .prog_i(flash_ctrl_i.prog),
      .pg_erase_i(flash_ctrl_i.pg_erase),
      .bk_erase_i(flash_ctrl_i.bk_erase),
      .addr_i(flash_ctrl_i.addr[0 +: PageW + WordW]),
      .prog_data_i(flash_ctrl_i.prog_data),
      .host_req_rdy_o(host_req_rdy[bank]),
      .host_req_done_o(host_req_done[bank]),
      .rd_done_o(rd_done[bank]),
      .prog_done_o(prog_done[bank]),
      .erase_done_o(erase_done[bank]),
      .rd_data_o(rd_data[bank]),
      .init_busy_o(init_busy[bank])
    );
  end

endmodule // flash_phy
