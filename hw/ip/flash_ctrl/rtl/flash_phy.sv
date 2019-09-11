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
  input flash_ctrl_pkg::flash_c2m_t flash_ctrl_i,
  output flash_ctrl_pkg::flash_m2c_t flash_ctrl_o
);

  // the primary function of flash phy, at the moment, is to redirect transactions to the correct
  // flash macro.  This is done at the flash_phy level and not the modeled prim_flash level to
  // ensure each prim_flash represents one bank of flash, and that there will not be blocking
  // behavior when the host reads from one flash bank while a write / erase is performed on another
  // bank.  If there is further non-blocking behavior at the page level, that is expected to be
  // modeled inside the prim_flash

  logic                 host_rd_pending;
  logic [BankW-1:0]     host_bank_sel, ctrl_bank_sel;
  logic [BankW-1:0]     host_last_bank_sel;
  logic [NumBanks-1:0]  host_req_rdy;
  logic [NumBanks-1:0]  host_req_done;
  logic [DataWidth-1:0] rd_data [NumBanks];
  logic [NumBanks-1:0]  rd_done;
  logic [NumBanks-1:0]  prog_done;
  logic [NumBanks-1:0]  erase_done;
  logic [NumBanks-1:0]  init_busy;
  logic                 host_rd_done;
  logic                 new_rd_rdy;


  assign host_bank_sel = host_addr_i[PageW + WordW +: BankW];
  assign ctrl_bank_sel = flash_ctrl_i.addr[PageW + WordW +: BankW];
  assign host_rd_done = host_rd_pending && host_req_done_o;

  // a new host read can be accepted if no host pending, or if current read is completing
  assign new_rd_rdy = !host_rd_pending | host_rd_done;

  // The host / controller arbitration is handled in prim_flash. This allows flash_phy to just
  // forward on the request such that controller activity on one bank does not block host activity
  // on another.
  //
  // Logic here is mainly tracking which bank host is currently reading, as the host request signals
  // do not hold until data return
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      host_last_bank_sel <= BankW'(0);
      host_rd_pending <= 1'b0;
    end else if (host_req_i && host_req_rdy_o) begin
      host_last_bank_sel <= host_bank_sel;
      host_rd_pending <= 1'b1;
    end else if (host_rd_done) begin
      //if host read finished and no other request waiting
      host_rd_pending <= 1'b0;
    end
  end

  // ready when prim_flash is ready and no ongoing host activity
  assign host_req_rdy_o = host_req_rdy[host_bank_sel] & new_rd_rdy & host_req_i;
  assign host_req_done_o = host_req_done[host_last_bank_sel];
  assign host_rdata_o = rd_data[host_last_bank_sel];

  assign flash_ctrl_o.rd_done = rd_done[ctrl_bank_sel];
  assign flash_ctrl_o.prog_done = prog_done[ctrl_bank_sel];
  assign flash_ctrl_o.erase_done = erase_done[ctrl_bank_sel];
  assign flash_ctrl_o.rd_data = rd_data[ctrl_bank_sel];
  assign flash_ctrl_o.init_busy = |init_busy;

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_flash_banks
    prim_flash #(
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth)
    ) u_flash (
      .clk_i,
      .rst_ni,
      .req_i(flash_ctrl_i.req & (ctrl_bank_sel == bank)),
      .host_req_i(host_req_i & (host_bank_sel == bank) & new_rd_rdy),
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
