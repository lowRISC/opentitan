// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rstmgr_fpv_tb;
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t;

  // Primary module clocks
  logic clk_i;
  logic rst_ni;
  logic clk_aon_i;
  logic clk_io_div4_i;
  logic clk_main_i;
  logic clk_io_i;
  logic clk_io_div2_i;
  logic clk_usb_i;
  logic clk_por_i;
  logic rst_por_ni;

  // POR input
  logic [PowerDomains-1:0] por_n_i;

  // Bus Interface
  tlul_pkg::tl_h2d_t tl_i;
  tlul_pkg::tl_d2h_t tl_o;

  // Alerts
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o;

  // Power Manager interface
  pwrmgr_pkg::pwr_rst_req_t pwr_i;
  pwrmgr_pkg::pwr_rst_rsp_t pwr_o;

  // Software initiated reset request
  mubi4_t sw_rst_req_o;

  // Interface to alert handler
  alert_handler_pkg::alert_crashdump_t alert_dump_i;

  // Interface to cpu crash dump
  rv_core_ibex_pkg::cpu_crash_dump_t cpu_dump_i;

  // DFT bypass
  logic scan_rst_ni;

  // SEC_CM: SCAN.INTERSIG.MUBI
  mubi4_t scanmode_i;

  // Reset asserted indications going to alert handler
  rstmgr_rst_en_t rst_en_o;

  // Reset outputs
  rstmgr_out_t resets_o;

  assign scanmode_i  = prim_mubi_pkg::MuBi4False;
  assign scan_rst_ni = 1'b1;

  rstmgr #(
  ) u_rstmgr (
      .alert_tx_o,
      .alert_rx_i,
      .por_n_i,
      .pwr_i,
      .pwr_o,
      .resets_o,
      .rst_en_o,
      .alert_dump_i,
      .cpu_dump_i,
      .sw_rst_req_o,
      .tl_i,
      .tl_o,
      .scanmode_i,
      .scan_rst_ni,

      // Clock and reset connections
      .clk_i,
      .clk_por_i,
      .clk_aon_i,
      .clk_main_i,
      .clk_io_i,
      .clk_usb_i,
      .clk_io_div2_i,
      .clk_io_div4_i,
      .rst_ni,
      .rst_por_ni
  );

endmodule
