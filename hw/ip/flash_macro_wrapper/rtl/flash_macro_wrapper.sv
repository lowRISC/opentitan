// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash macro wrapper
//

module flash_macro_wrapper
  import flash_ctrl_pkg::*;
  import flash_macro_wrapper_pkg::*;
  import flash_phy_macro_pkg::*;
#(
  parameter int NumBanks       = 2,  // number of banks
  parameter int InfosPerBank   = 1,  // info pages per bank
  parameter int InfoTypes      = 1,  // different info types
  parameter int InfoTypesWidth = 1,  // different info types
  parameter int PagesPerBank   = 256,// data pages per bank
  parameter int WordsPerPage   = 256,// words per page
  parameter int DataWidth      = 32, // bits per word
  parameter int TestModeWidth  = 2
) (
  input logic clk_i,
  input logic rst_ni,
  input flash_phy_macro_req_t flash_i,
  output flash_phy_macro_rsp_t flash_o,
  output flash_macro_status_t status_o,
  // life cycle interface
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input lc_ctrl_pkg::lc_tx_t lc_nvm_debug_en_i,
  input logic cio_tck_i,
  input logic cio_tdi_i,
  input logic cio_tms_i,
  output logic cio_tdo_o,
  output logic cio_tdo_en_o,
  input prim_mubi_pkg::mubi4_t bist_enable_i,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input logic scan_en_i,
  input logic scan_rst_ni,
  input logic power_ready_h_i,
  input logic power_down_h_i,
  inout [TestModeWidth-1:0] test_mode_a_io,
  inout test_voltage_h_io,
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  // Observability
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output fla_obs_t fla_obs_o
);
  import lc_ctrl_pkg::lc_tx_test_true_strict;

  lc_ctrl_pkg::lc_tx_t [FlashLcDftLast-1:0] lc_nvm_debug_en;
  prim_lc_sync #(
    .NumCopies(int'(FlashLcDftLast))
  ) u_lc_nvm_debug_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_nvm_debug_en_i),
    .lc_en_o(lc_nvm_debug_en)
  );

  logic tck;
  assign tck = cio_tck_i & lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTckSel]);

  logic tdi;
  assign tdi = cio_tdi_i & lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTdiSel]);

  logic tms;
  assign tms = cio_tms_i & lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTmsSel]);

  logic tdo;
  // Xor tdo to prevent this logic from getting removed in the open-source model.
  assign cio_tdo_o = tdo ^ lc_tx_test_true_strict(lc_nvm_debug_en[FlashLcTdoSel]);

  // if nvm debug is enabled, bist_enable_qual controls entry to flash test mode.
  // if nvm debug is disabled, bist_enable_qual is always turned off.
  prim_mubi_pkg::mubi4_t bist_enable_qual;
  assign bist_enable_qual = (lc_tx_test_true_strict(lc_nvm_debug_en[FlashBistSel])) ?
                            bist_enable_i :
                            prim_mubi_pkg::MuBi4False;

  // convert this into a tlul write later
  logic init;
  assign init = 1'b1;

  logic [NumBanks-1:0] init_busy;
  assign status_o.init_busy = |init_busy;

  // this represents the type of program operations that are supported
  assign status_o.prog_type_avail[FlashProgNormal] = 1'b1;
  assign status_o.prog_type_avail[FlashProgRepair] = 1'b1;

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_flash_banks

    flash_macro_bank #(
      .InfosPerBank(InfosPerBank),
      .InfoTypes(InfoTypes),
      .InfoTypesWidth(InfoTypesWidth),
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth)
    ) u_flash_macro_bank (
      .clk_i,
      .rst_ni,
      .rd_i(flash_i.bank_reqs[bank].rd_req),
      .prog_i(flash_i.bank_reqs[bank].prog_req),
      .prog_last_i(flash_i.bank_reqs[bank].prog_last),
      .prog_type_i(flash_i.bank_reqs[bank].prog_type),
      .pg_erase_i(flash_i.bank_reqs[bank].pg_erase_req),
      .bk_erase_i(flash_i.bank_reqs[bank].bk_erase_req),
      .erase_suspend_req_i(flash_i.bank_reqs[bank].erase_suspend_req),
      .he_i(flash_i.bank_reqs[bank].he),
      .addr_i(flash_i.bank_reqs[bank].addr),
      .part_i(flash_i.bank_reqs[bank].part),
      .info_sel_i(flash_i.bank_reqs[bank].info_sel),
      .prog_data_i(flash_i.bank_reqs[bank].prog_full_data),
      .ack_o(flash_o.bank_rsps[bank].ack),
      .done_o(flash_o.bank_rsps[bank].done),
      .rd_data_o(flash_o.bank_rsps[bank].rdata),
      .init_i(init),
      .init_busy_o(init_busy[bank]),
      .flash_power_ready_h_i (power_ready_h_i),
      .flash_power_down_h_i (power_down_h_i)
    );
  end

  logic unused_scanmode;
  logic unused_scan_en;
  logic unused_scan_rst_n;
  logic [TestModeWidth-1:0] unused_flash_test_mode;
  logic unused_flash_test_voltage;
  logic unused_tck;
  logic unused_tdi;
  logic unused_tms;
  logic unused_bist_enable_qual;

  assign unused_scanmode = ^scanmode_i;
  assign unused_scan_en = scan_en_i;
  assign unused_scan_rst_n = scan_rst_ni;
  assign unused_flash_test_mode = test_mode_a_io;
  assign unused_flash_test_voltage = test_voltage_h_io;
  assign unused_tck = tck;
  assign unused_tdi = tdi;
  assign unused_tms = tms;
  assign unused_bist_enable_qual = ^bist_enable_qual;
  assign tdo = '0;
  assign cio_tdo_en_o = '1;

  ////////////////////////////////////
  // TL-UL Test Interface Emulation //
  ////////////////////////////////////

  logic intg_err;
  flash_macro_wrapper_reg_pkg::flash_macro_wrapper_reg2hw_t reg2hw;
  flash_macro_wrapper_reg_pkg::flash_macro_wrapper_hw2reg_t hw2reg;

  // SEC_CM: REG.BUS.INTEGRITY
  flash_macro_wrapper_reg_top u_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i      (tl_i),
    .tl_o      (tl_o),
    .reg2hw    (reg2hw),
    .hw2reg    (hw2reg),
    .intg_err_o(intg_err)
  );

  logic unused_reg_sig;
  assign unused_reg_sig = ^reg2hw;
  assign hw2reg = '0;

  // open source model has no error response at the moment
  assign status_o.flash_err = 1'b0;

  assign status_o.fatal_alert = intg_err;
  assign status_o.recov_alert = 1'b0;

  logic unused_obs;
  assign unused_obs = |obs_ctrl_i;
  assign fla_obs_o = '0;

  // Assertions
  `ASSERT_KNOWN(PrimTlDValidKnownO_A,   tl_o.d_valid )
  `ASSERT_KNOWN(PrimTlAReadyKnownO_A,   tl_o.a_ready )
  `ASSERT_KNOWN_IF(PrimRspPayLoad_A,    tl_o, tl_o.d_valid)
  `ASSERT_KNOWN(TdoKnown_A,             cio_tdo_o        )
  `ASSERT(TdoOeIsOne_A,                 cio_tdo_en_o === 1'b1)

  `ASSERT_ERROR_TRIGGER_ERR(PrimRegWeOnehotCheck_A,
      u_reg_top.u_prim_reg_we_check.u_prim_onehot_check, status_o.fatal_alert, 0,
      `_SEC_CM_ALERT_MAX_CYC, err_o, `ASSERT_DEFAULT_CLK, `ASSERT_DEFAULT_RST)
  `ASSUME_FPV(PrimRegWeOneHotCheck_ATriggerAfterAlertInit_S,
              $stable(rst_ni) == 0 |-> u_state_regs.err_o == 0 [*10])

endmodule : flash_macro_wrapper
