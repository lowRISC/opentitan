// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Overall flash wrapper
//

module prim_generic_flash #(
  parameter int NumBanks       = 2,  // number of banks
  parameter int InfosPerBank   = 1,  // info pages per bank
  parameter int InfoTypes      = 1,  // different info types
  parameter int InfoTypesWidth = 1,  // different info types
  parameter int PagesPerBank   = 256,// data pages per bank
  parameter int WordsPerPage   = 256,// words per page
  parameter int DataWidth      = 32, // bits per word
  parameter int TestModeWidth  = 2
) (
  input clk_i,
  input rst_ni,
  input flash_phy_pkg::flash_phy_prim_flash_req_t [NumBanks-1:0] flash_req_i,
  output flash_phy_pkg::flash_phy_prim_flash_rsp_t [NumBanks-1:0] flash_rsp_o,
  output logic [flash_phy_pkg::ProgTypes-1:0] prog_type_avail_o,
  output init_busy_o,
  input tck_i,
  input tdi_i,
  input tms_i,
  output logic tdo_o,
  input prim_mubi_pkg::mubi4_t bist_enable_i,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input scan_en_i,
  input scan_rst_ni,
  input flash_power_ready_h_i,
  input flash_power_down_h_i,
  inout [TestModeWidth-1:0] flash_test_mode_a_io,
  inout flash_test_voltage_h_io,
  output logic flash_err_o,
  // Alert indication (to be connected to alert sender in the instantiating IP)
  output logic fatal_alert_o,
  output logic recov_alert_o,
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  // Observability
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0] fla_obs_o,
  input  devmode_i
);

  logic unused_devmode;
  assign unused_devmode = devmode_i;

  // convert this into a tlul write later
  logic init;
  assign init = 1'b1;

  logic [NumBanks-1:0] init_busy;
  assign init_busy_o = |init_busy;

  // this represents the type of program operations that are supported
  assign prog_type_avail_o[flash_ctrl_pkg::FlashProgNormal] = 1'b1;
  assign prog_type_avail_o[flash_ctrl_pkg::FlashProgRepair] = 1'b1;

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_prim_flash_banks

    prim_generic_flash_bank #(
      .InfosPerBank(InfosPerBank),
      .InfoTypes(InfoTypes),
      .InfoTypesWidth(InfoTypesWidth),
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth)
    ) u_prim_flash_bank (
      .clk_i,
      .rst_ni,
      .rd_i(flash_req_i[bank].rd_req),
      .prog_i(flash_req_i[bank].prog_req),
      .prog_last_i(flash_req_i[bank].prog_last),
      .prog_type_i(flash_req_i[bank].prog_type),
      .pg_erase_i(flash_req_i[bank].pg_erase_req),
      .bk_erase_i(flash_req_i[bank].bk_erase_req),
      .erase_suspend_req_i(flash_req_i[bank].erase_suspend_req),
      .he_i(flash_req_i[bank].he),
      .addr_i(flash_req_i[bank].addr),
      .part_i(flash_req_i[bank].part),
      .info_sel_i(flash_req_i[bank].info_sel),
      .prog_data_i(flash_req_i[bank].prog_full_data),
      .ack_o(flash_rsp_o[bank].ack),
      .done_o(flash_rsp_o[bank].done),
      .rd_data_o(flash_rsp_o[bank].rdata),
      .init_i(init),
      .init_busy_o(init_busy[bank]),
      .flash_power_ready_h_i,
      .flash_power_down_h_i
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

  assign unused_scanmode = ^scanmode_i;
  assign unused_scan_en = scan_en_i;
  assign unused_scan_rst_n = scan_rst_ni;
  assign unused_flash_test_mode = flash_test_mode_a_io;
  assign unused_flash_test_voltage = flash_test_voltage_h_io;
  assign unused_tck = tck_i;
  assign unused_tdi = tdi_i;
  assign unused_tms = tms_i;
  assign tdo_o = '0;

  ////////////////////////////////////
  // TL-UL Test Interface Emulation //
  ////////////////////////////////////

  logic intg_err;
  flash_ctrl_reg_pkg::flash_ctrl_prim_reg2hw_t reg2hw;
  flash_ctrl_reg_pkg::flash_ctrl_prim_hw2reg_t hw2reg;
  flash_ctrl_prim_reg_top u_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i      (tl_i),
    .tl_o      (tl_o),
    .reg2hw    (reg2hw),
    .hw2reg    (hw2reg),
    .intg_err_o(intg_err),
    .devmode_i (1'b1)
  );

  logic unused_reg_sig;
  assign unused_reg_sig = ^reg2hw;
  assign hw2reg = '0;

  logic unused_bist_enable;
  assign unused_bist_enable = ^bist_enable_i;

  // open source model has no error response at the moment
  assign flash_err_o = 1'b0;

  assign fatal_alert_o = intg_err;
  assign recov_alert_o = 1'b0;

  logic unused_obs;
  assign unused_obs = |obs_ctrl_i;
  assign fla_obs_o = '0;


endmodule // prim_generic_flash
