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

module flash_phy import flash_ctrl_pkg::*; (
  input clk_i,
  input rst_ni,
  input host_req_i,
  input [BusAddrW-1:0] host_addr_i,
  output logic host_req_rdy_o,
  output logic host_req_done_o,
  output logic [BusWidth-1:0] host_rdata_o,
  output logic host_rderr_o,
  input flash_req_t flash_ctrl_i,
  output flash_rsp_t flash_ctrl_o,
  input scanmode_i,
  input scan_rst_ni,
  input flash_power_ready_h_i,
  input flash_power_down_h_i,
  input [1:0] flash_test_mode_a_i,
  input flash_test_voltage_h_i,
  input flash_bist_enable_i,
  input lc_ctrl_pkg::lc_tx_t lc_nvm_debug_en_i,
  input jtag_pkg::jtag_req_t jtag_req_i,
  output jtag_pkg::jtag_rsp_t jtag_rsp_o
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
  logic [BusWidth-1:0]  host_rsp_data [NumBanks];
  logic [NumBanks-1:0]  host_rsp_err;
  logic                 seq_fifo_rdy;
  logic                 seq_fifo_pending;

  // flash_ctrl to flash_phy interface
  logic [BankW-1:0]     ctrl_bank_sel;
  logic [NumBanks-1:0]  rd_done;
  logic [NumBanks-1:0]  prog_done;
  logic [NumBanks-1:0]  erase_done;
  logic                 init_busy;
  logic [ProgTypes-1:0] prog_type_avail;

  // common interface
  logic [BusWidth-1:0] rd_data [NumBanks];
  logic [NumBanks-1:0] rd_err;

  // select which bank each is operating on
  assign host_bank_sel = host_req_i ? host_addr_i[BusAddrW-1 -: BankW] : '0;
  assign ctrl_bank_sel = flash_ctrl_i.addr[BusAddrW-1 -: BankW];

  // accept transaction if bank is ready and previous response NOT pending
  assign host_req_rdy_o = host_req_rdy[host_bank_sel] & host_rsp_avail[host_bank_sel] &
                          seq_fifo_rdy;

  assign host_req_done_o = seq_fifo_pending & host_rsp_vld[rsp_bank_sel];
  assign host_rderr_o = host_rsp_err[rsp_bank_sel];
  assign host_rdata_o = host_rsp_data[rsp_bank_sel];

  // all banks are assumed to be the same in terms of prog_type support
  assign flash_ctrl_o.prog_type_avail = prog_type_avail;
  assign flash_ctrl_o.rd_done = rd_done[ctrl_bank_sel];
  assign flash_ctrl_o.prog_done = prog_done[ctrl_bank_sel];
  assign flash_ctrl_o.erase_done = erase_done[ctrl_bank_sel];
  assign flash_ctrl_o.rd_data = rd_data[ctrl_bank_sel];
  assign flash_ctrl_o.rd_err = rd_err[ctrl_bank_sel];
  assign flash_ctrl_o.init_busy = init_busy;

  // This fifo holds the expected return order
  prim_fifo_sync #(
    .Width   (BankW),
    .Pass    (0),
    .Depth   (SeqFifoDepth)
  ) u_bank_sequence_fifo (
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

  // Generate host scramble_en indication, broadcasted to all banks
  localparam int TotalRegions = MpRegions + 1;
  logic host_scramble_en, host_ecc_en;
  data_region_attr_t region_attrs [TotalRegions];
  mp_region_cfg_t region_cfg, unused_cfg;

  for(genvar i = 0; i < TotalRegions; i++) begin : gen_region_attrs
    assign region_attrs[i].phase = PhaseInvalid;
    assign region_attrs[i].cfg = flash_ctrl_i.region_cfgs[i];
  end

  // the region decode only accepts page address
  flash_mp_data_region_sel #(
    .Regions(TotalRegions)
  ) u_region_sel (
    .req_i(host_req_i),
    .phase_i(PhaseInvalid),
    .addr_i(host_addr_i[BusAddrW-1 -: AllPagesW]),
    .region_attrs_i(region_attrs),
    .sel_cfg_o(region_cfg)
  );

  // most attributes are unused
  assign unused_cfg = region_cfg;

  // only scramble/ecc attributes are looked at
  assign host_scramble_en = region_cfg.scramble_en.q;
  assign host_ecc_en = region_cfg.ecc_en.q;

  // Prim flash to flash_phy_core connections
  flash_phy_pkg::flash_phy_prim_flash_req_t [NumBanks-1:0] prim_flash_req;
  flash_phy_pkg::flash_phy_prim_flash_rsp_t [NumBanks-1:0] prim_flash_rsp;

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_flash_cores

    // pop if the response came from the appropriate fifo
    assign host_rsp_ack[bank] = host_req_done_o & (rsp_bank_sel == bank);

    prim_fifo_sync #(
      .Width   (BusWidth + 1),
      .Pass    (1'b1),
      .Depth   (FlashMacroOustanding)
    ) u_host_rsp_fifo (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(host_req_done[bank]),
      .wready_o(host_rsp_avail[bank]),
      .wdata_i ({rd_err[bank], rd_data[bank]}),
      .depth_o (),
      .rvalid_o(host_rsp_vld[bank]),
      .rready_i(host_rsp_ack[bank]),
      .rdata_o ({host_rsp_err[bank], host_rsp_data[bank]})
    );

    logic host_req;
    logic ctrl_req;
    assign host_req = host_req_i & (host_bank_sel == bank) & host_rsp_avail[bank];
    assign ctrl_req = flash_ctrl_i.req & (ctrl_bank_sel == bank);

    flash_phy_core u_core (
      .clk_i,
      .rst_ni,
      .req_i(ctrl_req),
      .scramble_en_i(flash_ctrl_i.scramble_en),
      .ecc_en_i(flash_ctrl_i.ecc_en),
      .he_en_i(flash_ctrl_i.he_en),
      // host request must be suppressed if response fifo cannot hold more
      // otherwise the flash_phy_core and flash_phy will get out of sync
      .host_req_i(host_req),
      .host_scramble_en_i(host_scramble_en),
      .host_ecc_en_i(host_ecc_en),
      .host_addr_i(host_addr_i[0 +: BusBankAddrW]),
      .rd_i(flash_ctrl_i.rd),
      .prog_i(flash_ctrl_i.prog),
      .pg_erase_i(flash_ctrl_i.pg_erase),
      .bk_erase_i(flash_ctrl_i.bk_erase),
      .erase_suspend_req_i(flash_ctrl_i.erase_suspend),
      .part_i(flash_ctrl_i.part),
      .info_sel_i(flash_ctrl_i.info_sel),
      .addr_i(flash_ctrl_i.addr[0 +: BusBankAddrW]),
      .prog_data_i(flash_ctrl_i.prog_data),
      .prog_last_i(flash_ctrl_i.prog_last),
      .prog_type_i(flash_ctrl_i.prog_type),
      .addr_key_i(flash_ctrl_i.addr_key),
      .data_key_i(flash_ctrl_i.data_key),
      .rd_buf_en_i(flash_ctrl_i.rd_buf_en),
      .host_req_rdy_o(host_req_rdy[bank]),
      .host_req_done_o(host_req_done[bank]),
      .rd_done_o(rd_done[bank]),
      .prog_done_o(prog_done[bank]),
      .erase_done_o(erase_done[bank]),
      .rd_data_o(rd_data[bank]),
      .rd_err_o(rd_err[bank]),
      .prim_flash_req_o(prim_flash_req[bank]),
      .prim_flash_rsp_i(prim_flash_rsp[bank])
    );
  end // block: gen_flash_banks

  // life cycle handling
  logic tdo;
  lc_ctrl_pkg::lc_tx_t [FlashLcDftLast-1:0] lc_nvm_debug_en;

  assign jtag_rsp_o.tdo = tdo & (lc_nvm_debug_en[FlashLcTdoSel] == lc_ctrl_pkg::On);

  prim_lc_sync #(
    .NumCopies(int'(FlashLcDftLast))
  ) u_lc_nvm_debug_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_nvm_debug_en_i),
    .lc_en_o(lc_nvm_debug_en)
  );

  prim_flash #(
    .NumBanks(NumBanks),
    .InfosPerBank(InfosPerBank),
    .InfoTypes(InfoTypes),
    .InfoTypesWidth(InfoTypesWidth),
    .PagesPerBank(PagesPerBank),
    .WordsPerPage(WordsPerPage),
    .DataWidth(flash_phy_pkg::FullDataWidth),
    .MetaDataWidth(MetaDataWidth)
  ) u_flash (
    .clk_i,
    .rst_ni,
    .tl_i(flash_ctrl_i.tl_flash_c2p),
    .tl_o(flash_ctrl_o.tl_flash_p2c),
    .flash_req_i(prim_flash_req),
    .flash_rsp_o(prim_flash_rsp),
    .prog_type_avail_o(prog_type_avail),
    .init_busy_o(init_busy),
    .tck_i(jtag_req_i.tck & (lc_nvm_debug_en[FlashLcTckSel] == lc_ctrl_pkg::On)),
    .tdi_i(jtag_req_i.tdi & (lc_nvm_debug_en[FlashLcTdiSel] == lc_ctrl_pkg::On)),
    .tms_i(jtag_req_i.tms & (lc_nvm_debug_en[FlashLcTmsSel] == lc_ctrl_pkg::On)),
    .tdo_o(tdo),
    .bist_enable_i(flash_bist_enable_i & (lc_nvm_debug_en[FlashBistSel] == lc_ctrl_pkg::On)),
    .scanmode_i,
    .scan_rst_ni,
    .flash_power_ready_h_i,
    .flash_power_down_h_i,
    .flash_test_mode_a_i,
    .flash_test_voltage_h_i
  );

  logic unused_trst_n;
  assign unused_trst_n = jtag_req_i.trst_n;
  assign jtag_rsp_o.tdo_oe = 1'b1;

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  /////////////////////////////////////////////

  // Add some assertions regarding response ordering

endmodule // flash_phy
