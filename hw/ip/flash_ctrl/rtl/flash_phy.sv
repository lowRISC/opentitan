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
  import prim_mubi_pkg::mubi4_t;
#(
  parameter bit SecScrambleEn = 1'b1
)
(
  input clk_i,
  input rst_ni,
  input host_req_i,
  input [BusAddrW-1:0] host_addr_i,
  output logic host_req_rdy_o,
  output logic host_req_done_o,
  output logic [BusFullWidth-1:0] host_rdata_o,
  output logic host_rderr_o,
  input flash_req_t flash_ctrl_i,
  output flash_rsp_t flash_ctrl_o,
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  input mubi4_t scanmode_i,
  input scan_en_i,
  input scan_rst_ni,
  input flash_power_ready_h_i,
  input flash_power_down_h_i,
  inout [1:0] flash_test_mode_a_io,
  inout flash_test_voltage_h_io,
  input mubi4_t flash_bist_enable_i,
  input lc_ctrl_pkg::lc_tx_t lc_nvm_debug_en_i,
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0] fla_obs_o,
  output logic fatal_prim_flash_alert_o,
  output logic recov_prim_flash_alert_o
);

  import prim_mubi_pkg::MuBi4False;

  // Flash macro outstanding refers to how many reads we allow a macro to move ahead of an
  // in order blocking read. Since the data cannot be returned out of order, this simply
  // does the reads in advance and store them in a FIFO
  localparam int FlashMacroOustanding = 1;
  localparam int SeqFifoDepth = FlashMacroOustanding * NumBanks;

  // flash_phy forwards incoming host transactions to the appropriate bank.  However, depending
  // on the transaction type, the completion times may differ (for example, a transaction
  // requiring de-scramble will take significantly longer than one that hits in the read buffers).
  // This implies that it is possible for flash_phy to forward one transaction to bank N and another
  // to bank N+1 only for bank N+1 to finish its transaction first.
  //
  // This suggests that even though transactions are received in-order, they can complete out of
  // order.  Thus it is the responsibility of the flash_phy to sequence the responses correctly.
  // For banks that have finished ahead of time, it is also important to hold their output until
  // consumption by the host.
  //
  // The sequence fifo below holds the correct response order, while each flash_phy_core is
  // paired with a small passthrough response FIFO to hold the data if necessary.
  // If one bank finishes "ahead" of schedule, the response FIFO will hold the response, and no new
  // transactions will be issued to that bank until the response is consumed by the host.

  // host to flash_phy interface
  logic [BankW-1:0]        host_bank_sel;
  logic [BankW-1:0]        rsp_bank_sel;
  logic [NumBanks-1:0]     host_req_rdy;
  logic [NumBanks-1:0]     host_req_done;
  logic [NumBanks-1:0]     host_rsp_avail;
  logic [NumBanks-1:0]     host_rsp_vld;
  logic [NumBanks-1:0]     host_rsp_ack;
  logic [BusFullWidth-1:0] host_rsp_data [NumBanks];
  logic [NumBanks-1:0]     host_rsp_err;
  logic                    seq_fifo_rdy;
  logic                    seq_fifo_pending;

  // flash_ctrl to flash_phy interface
  logic [BankW-1:0]     ctrl_bank_sel;
  logic [NumBanks-1:0]  rd_done;
  logic [NumBanks-1:0]  prog_done;
  logic [NumBanks-1:0]  erase_done;
  logic                 init_busy;
  logic [ProgTypes-1:0] prog_type_avail;

  // common interface
  logic [BusFullWidth-1:0] rd_data [NumBanks];
  logic [NumBanks-1:0] rd_err;
  logic [NumBanks-1:0] spurious_acks;

  // fsm error per bank
  logic [NumBanks-1:0] fsm_err;

  // integrity error per bank
  logic [NumBanks-1:0] prog_intg_err;
  logic [NumBanks-1:0] relbl_ecc_err;
  logic [NumBanks-1:0] intg_ecc_err;

  // consistency error per bank
  logic [NumBanks-1:0] arb_err;
  logic [NumBanks-1:0] host_gnt_err;

  // fifo error per bank
  logic [NumBanks-1:0]     rsp_fifo_err;
  logic [NumBanks-1:0]     core_fifo_err;

  // outstanding count error per bank
  logic [NumBanks-1:0]     cnt_err;

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
  assign flash_ctrl_o.prog_intg_err = |prog_intg_err;
  assign flash_ctrl_o.storage_relbl_err = |relbl_ecc_err;
  assign flash_ctrl_o.storage_intg_err = |intg_ecc_err;
  assign flash_ctrl_o.fsm_err = |fsm_err;
  assign flash_ctrl_o.spurious_ack = |spurious_acks;
  assign flash_ctrl_o.arb_err = |arb_err;
  assign flash_ctrl_o.host_gnt_err = |{host_gnt_err, cnt_err} ;
  assign flash_ctrl_o.fifo_err = |{rsp_fifo_err, core_fifo_err};


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
    .full_o (),
    .rvalid_o(seq_fifo_pending),
    .rready_i(host_req_done_o),
    .rdata_o (rsp_bank_sel),
    .err_o   ()
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
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_and_hi;

  assign host_scramble_en = mubi4_test_true_strict(
                              mubi4_and_hi(region_cfg.scramble_en, region_cfg.en));
  assign host_ecc_en = mubi4_test_true_strict(mubi4_and_hi(region_cfg.ecc_en, region_cfg.en));

  // Prim flash to flash_phy_core connections
  flash_phy_pkg::flash_phy_prim_flash_req_t [NumBanks-1:0] prim_flash_req;
  flash_phy_pkg::flash_phy_prim_flash_rsp_t [NumBanks-1:0] prim_flash_rsp;
  logic [NumBanks-1:0] ecc_single_err;
  logic [NumBanks-1:0][BusAddrW-1:0] ecc_addr;

  assign flash_ctrl_o.ecc_single_err = ecc_single_err;
  assign flash_ctrl_o.ecc_addr = ecc_addr;

  mubi4_t [NumBanks-1:0] flash_disable;
  prim_mubi4_sync #(
    .NumCopies(NumBanks),
    .AsyncOn(0)
  ) u_disable_buf (
    .clk_i,
    .rst_ni,
    .mubi_i(flash_ctrl_i.flash_disable),
    .mubi_o(flash_disable)
  );


  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_flash_cores

    // pop if the response came from the appropriate fifo
    assign host_rsp_ack[bank] = host_req_done_o & (rsp_bank_sel == bank);

    prim_fifo_sync #(
      .Width   (BusFullWidth + 1),
      .Pass    (1'b1),
      .Depth   (FlashMacroOustanding),
      .Secure  (1'b1) // SEC_CM: FIFO.CTR.REDUN
    ) u_host_rsp_fifo (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(host_req_done[bank]),
      .wready_o(host_rsp_avail[bank]),
      .wdata_i ({rd_err[bank], rd_data[bank]}),
      .depth_o (),
      .full_o (),
      .rvalid_o(host_rsp_vld[bank]),
      .rready_i(host_rsp_ack[bank]),
      .rdata_o ({host_rsp_err[bank], host_rsp_data[bank]}),
      .err_o   (rsp_fifo_err[bank])
    );

    logic host_req;
    logic ctrl_req;
    assign host_req = host_req_i & (host_bank_sel == bank) & host_rsp_avail[bank];
    assign ctrl_req = flash_ctrl_i.req & (ctrl_bank_sel == bank);
    assign ecc_addr[bank][BusBankAddrW +: BankW] = bank;

    flash_phy_core #(
      .SecScrambleEn(SecScrambleEn)
    ) u_core (
      .clk_i,
      .rst_ni,
      // integrity error is either from host or from controller
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
      .rand_addr_key_i(flash_ctrl_i.rand_addr_key),
      .rand_data_key_i(flash_ctrl_i.rand_data_key),
      .rd_buf_en_i(flash_ctrl_i.rd_buf_en),
      .host_req_rdy_o(host_req_rdy[bank]),
      .host_req_done_o(host_req_done[bank]),
      .rd_done_o(rd_done[bank]),
      .prog_done_o(prog_done[bank]),
      .erase_done_o(erase_done[bank]),
      .rd_data_o(rd_data[bank]),
      .rd_err_o(rd_err[bank]),
      .flash_disable_i(flash_disable[bank]),
      .prim_flash_req_o(prim_flash_req[bank]),
      .prim_flash_rsp_i(prim_flash_rsp[bank]),
      .ecc_single_err_o(ecc_single_err[bank]),
      .ecc_addr_o(ecc_addr[bank][BusBankAddrW-1:0]),
      .fsm_err_o(fsm_err[bank]),
      .prog_intg_err_o(prog_intg_err[bank]),
      .relbl_ecc_err_o(relbl_ecc_err[bank]),
      .intg_ecc_err_o(intg_ecc_err[bank]),
      .spurious_ack_o(spurious_acks[bank]),
      .arb_err_o(arb_err[bank]),
      .host_gnt_err_o(host_gnt_err[bank]),
      .fifo_err_o(core_fifo_err[bank]),
      .cnt_err_o(cnt_err[bank])
    );
  end // block: gen_flash_banks

  // life cycle handling
  logic tdo;
  lc_ctrl_pkg::lc_tx_t [FlashLcDftLast-1:0] lc_nvm_debug_en;

  assign flash_ctrl_o.jtag_rsp.tdo = tdo & (lc_nvm_debug_en[FlashLcTdoSel] == lc_ctrl_pkg::On);

  prim_lc_sync #(
    .NumCopies(int'(FlashLcDftLast))
  ) u_lc_nvm_debug_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_nvm_debug_en_i),
    .lc_en_o(lc_nvm_debug_en)
  );

  import lc_ctrl_pkg::lc_tx_test_true_strict;
  // if nvm debug is enabled, flash_bist_enable controls entry to flash test mode.
  // if nvm debug is disabled, flash_bist_enable is always turned off.
  mubi4_t bist_enable_qual;
  assign bist_enable_qual = (lc_tx_test_true_strict(lc_nvm_debug_en[FlashBistSel])) ?
                            flash_bist_enable_i :
                            MuBi4False;

  prim_flash #(
    .NumBanks(NumBanks),
    .InfosPerBank(InfosPerBank),
    .InfoTypes(InfoTypes),
    .InfoTypesWidth(InfoTypesWidth),
    .PagesPerBank(PagesPerBank),
    .WordsPerPage(WordsPerPage),
    .DataWidth(flash_phy_pkg::FullDataWidth)
  ) u_flash (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .devmode_i(1'b1),
    .flash_req_i(prim_flash_req),
    .flash_rsp_o(prim_flash_rsp),
    .prog_type_avail_o(prog_type_avail),
    .init_busy_o(init_busy),
    .tck_i(flash_ctrl_i.jtag_req.tck & lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTckSel])),
    .tdi_i(flash_ctrl_i.jtag_req.tdi & lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTdiSel])),
    .tms_i(flash_ctrl_i.jtag_req.tms & lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTmsSel])),
    .tdo_o(tdo),
    .bist_enable_i(bist_enable_qual),
    .obs_ctrl_i,
    .fla_obs_o,
    .scanmode_i,
    .scan_en_i,
    .scan_rst_ni,
    .flash_power_ready_h_i,
    .flash_power_down_h_i,
    .flash_test_mode_a_io,
    .flash_test_voltage_h_io,
    .flash_err_o(flash_ctrl_o.macro_err),
    .fatal_alert_o(fatal_prim_flash_alert_o),
    .recov_alert_o(recov_prim_flash_alert_o)
  );
  logic unused_alert;
  assign unused_alert = flash_ctrl_i.alert_trig & flash_ctrl_i.alert_ack;

  logic unused_trst_n;
  assign unused_trst_n = flash_ctrl_i.jtag_req.trst_n;
  assign flash_ctrl_o.jtag_rsp.tdo_oe = 1'b1;

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  /////////////////////////////////////////////

  // Add some assertions regarding response ordering

endmodule // flash_phy
