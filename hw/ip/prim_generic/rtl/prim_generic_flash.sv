// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Overall flash wrapper
//

module prim_generic_flash #(
  parameter int NumBanks      = 2,   // number of banks
  parameter int InfosPerBank  = 1,   // info pages per bank
  parameter int PagesPerBank  = 256, // data pages per bank
  parameter int WordsPerPage  = 256, // words per page
  parameter int DataWidth     = 32,  // bits per word
  parameter int MetaDataWidth = 12,  // metadata such as ECC
  parameter int TestModeWidth = 2
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
  input scanmode_i,
  input scan_rst_ni,
  input flash_power_ready_h_i,
  input flash_power_down_h_i,
  input [TestModeWidth-1:0] flash_test_mode_a_i,
  input flash_test_voltage_h_i
);

  logic [NumBanks-1:0] init_busy;
  assign init_busy_o = |init_busy;

  // this represents the type of program operations that are supported
  assign prog_type_avail_o[flash_ctrl_pkg::FlashProgNormal] = 1'b1;
  assign prog_type_avail_o[flash_ctrl_pkg::FlashProgRepair] = 1'b1;

  for (genvar bank = 0; bank < NumBanks; bank++) begin : gen_prim_flash_banks
    prim_generic_flash_bank #(
      .InfosPerBank(InfosPerBank),
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth),
      .MetaDataWidth(MetaDataWidth)
    ) u_prim_flash_bank (
      .clk_i,
      .rst_ni,
      .rd_i(flash_req_i[bank].rd_req),
      .prog_i(flash_req_i[bank].prog_req),
      .prog_last_i(flash_req_i[bank].prog_last),
      .prog_type_i(flash_req_i[bank].prog_type),
      .pg_erase_i(flash_req_i[bank].pg_erase_req),
      .bk_erase_i(flash_req_i[bank].bk_erase_req),
      .addr_i(flash_req_i[bank].addr),
      .part_i(flash_req_i[bank].part),
      .prog_data_i(flash_req_i[bank].prog_full_data),
      .ack_o(flash_rsp_o[bank].ack),
      .done_o(flash_rsp_o[bank].done),
      .rd_data_o(flash_rsp_o[bank].rdata),
      .init_busy_o(init_busy[bank]),
      .flash_power_ready_h_i,
      .flash_power_down_h_i
    );
  end

  logic unused_scanmode;
  logic unused_scan_rst_n;
  logic [TestModeWidth-1:0] unused_flash_test_mode;
  logic unused_flash_test_voltage;
  logic unused_tck;
  logic unused_tdi;
  logic unused_tms;

  assign unused_scanmode = scanmode_i;
  assign unused_scan_rst_n = scan_rst_ni;
  assign unused_flash_test_mode = flash_test_mode_a_i;
  assign unused_flash_test_voltage = flash_test_voltage_h_i;
  assign unused_tck = tck_i;
  assign unused_tdi = tdi_i;
  assign unused_tms = tms_i;
  assign tdo_o = '0;

endmodule // prim_generic_flash
