// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Module
//
//
// Flash phy represents the top level open source wrapper for a proprietary flash
// module.
// The top level flash_phy is only responsible for dispatching transactions and
// correctly collecting the responses in order.

module flash_phy
import flash_ctrl_pkg::*;
(
    input                             clk_i,
    input                             rst_ni,
    input                             host_req_i,
    input              [BusAddrW-1:0] host_addr_i,
    output logic                      host_req_rdy_o,
    output logic                      host_req_done_o,
    output logic       [BusWidth-1:0] host_rdata_o,
    input  flash_req_t                flash_ctrl_i,
    output flash_rsp_t                flash_ctrl_o
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
  logic [BankW-1:0] host_bank_sel;
  logic [BankW-1:0] rsp_bank_sel;
  logic [NumBanks-1:0] host_req_rdy;
  logic [NumBanks-1:0] host_req_done;
  logic [NumBanks-1:0] host_rsp_avail;
  logic [NumBanks-1:0] host_rsp_vld;
  logic [NumBanks-1:0] host_rsp_ack;
  logic [BusWidth-1:0] host_rsp_data[NumBanks];
  logic seq_fifo_rdy;
  logic seq_fifo_pending;


  // flash_ctrl to flash_phy interface
  logic [BankW-1:0] ctrl_bank_sel;
  logic [NumBanks-1:0] rd_done;
  logic [NumBanks-1:0] prog_done;
  logic [NumBanks-1:0] erase_done;
  logic [NumBanks-1:0] init_busy;

  // common interface
  logic [BusWidth-1:0] rd_data[NumBanks];

  // select which bank each is operating on
  assign host_bank_sel = host_req_i ? host_addr_i[BusAddrW - 1 -: BankW] : '0;
  assign ctrl_bank_sel = flash_ctrl_i.addr[BusAddrW - 1 -: BankW];

  // accept transaction if bank is ready and previous response NOT pending
  assign
      host_req_rdy_o = host_req_rdy[host_bank_sel] & host_rsp_avail[host_bank_sel] & seq_fifo_rdy;

  assign host_req_done_o = seq_fifo_pending & host_rsp_vld[rsp_bank_sel];
  assign host_rdata_o = host_rsp_data[rsp_bank_sel];

  assign flash_ctrl_o.rd_done = rd_done[ctrl_bank_sel];
  assign flash_ctrl_o.prog_done = prog_done[ctrl_bank_sel];
  assign flash_ctrl_o.erase_done = erase_done[ctrl_bank_sel];
  assign flash_ctrl_o.rd_data = rd_data[ctrl_bank_sel];
  assign flash_ctrl_o.init_busy = |init_busy;

  // This fifo holds the expected return order
  prim_fifo_sync #(
      .Width(BankW),
      .Pass(0),
      .Depth(SeqFifoDepth)
  ) i_bank_sequence_fifo (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(host_req_i & host_req_rdy_o),
      .wready_o(seq_fifo_rdy),
      .wdata_i (host_bank_sel),
      .depth_o (),
      .rvalid_o(seq_fifo_pending),
      .rready_i(host_req_done_o),
      .rdata_o (rsp_bank_sel)
  );

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_flash_banks

    // pop if the response came from the appropriate fifo
    assign host_rsp_ack[bank] = host_req_done_o & (rsp_bank_sel == bank);

    prim_fifo_sync #(
        .Width(BusWidth),
        .Pass(1'b1),
        .Depth(FlashMacroOustanding)
    ) i_host_rsp_fifo (
        .clk_i,
        .rst_ni,
        .clr_i   (1'b0),
        .wvalid_i(host_req_done[bank]),
        .wready_o(host_rsp_avail[bank]),
        .wdata_i (rd_data[bank]),
        .depth_o (),
        .rvalid_o(host_rsp_vld[bank]),
        .rready_i(host_rsp_ack[bank]),
        .rdata_o (host_rsp_data[bank])
    );

    logic host_req;
    logic ctrl_req;
    logic host_scramble_en;
    logic ctrl_scramble_en;

    assign host_req = host_req_i & (host_bank_sel == bank) & host_rsp_avail[bank];
    assign ctrl_req = flash_ctrl_i.req & (ctrl_bank_sel == bank);

    // #2630: Temporary scramble enable logic on one of the banks until register configuration
    // is setup.
    assign host_scramble_en = host_req & host_addr_i[BusAddrW - 1 -: BankW] == 1;
    assign ctrl_scramble_en = ctrl_req & flash_ctrl_i.addr[BusAddrW - 1 -: BankW] == 1;

    flash_phy_core i_core (
        .clk_i,
        .rst_ni,
        .scramble_en_i  (flash_ctrl_i.scramble_en & (host_scramble_en | ctrl_scramble_en)),
        .req_i          (ctrl_req),
        // host request must be suppressed if response fifo cannot hold more
        // otherwise the flash_phy_core and flash_phy will get out of sync
        .host_req_i     (host_req),
        .host_addr_i    (host_addr_i[0 +: BusBankAddrW]),
        .rd_i           (flash_ctrl_i.rd),
        .prog_i         (flash_ctrl_i.prog),
        .pg_erase_i     (flash_ctrl_i.pg_erase),
        .bk_erase_i     (flash_ctrl_i.bk_erase),
        .part_i         (flash_ctrl_i.part),
        .addr_i         (flash_ctrl_i.addr[0 +: BusBankAddrW]),
        .prog_data_i    (flash_ctrl_i.prog_data),
        .prog_last_i    (flash_ctrl_i.prog_last),
        .addr_key_i     (flash_ctrl_i.addr_key),
        .data_key_i     (flash_ctrl_i.data_key),
        .host_req_rdy_o (host_req_rdy[bank]),
        .host_req_done_o(host_req_done[bank]),
        .rd_done_o      (rd_done[bank]),
        .prog_done_o    (prog_done[bank]),
        .erase_done_o   (erase_done[bank]),
        .rd_data_o      (rd_data[bank]),
        .init_busy_o    (init_busy[bank])
    );
  end

endmodule  // flash_phy
