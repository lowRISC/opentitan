// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for pinmux.
// Intended to be used with a formal tool.

module pinmux_tb
  import pinmux_pkg::*;
  import pinmux_reg_pkg::*;
  import prim_pad_wrapper_pkg::*;
#(
  parameter target_cfg_t TargetCfg = DefaultTargetCfg,
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input  clk_i,
  input  rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input  clk_aon_i,
  input  rst_aon_ni,
  output logic pin_wkup_req_o,
  output logic usb_wkup_req_o,
  input  sleep_en_i,
  input  strap_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  output dft_strap_test_req_t dft_strap_test_o,
  input  dft_hold_tap_sel_i,
  output jtag_pkg::jtag_req_t lc_jtag_o,
  input jtag_pkg::jtag_rsp_t lc_jtag_i,
  output jtag_pkg::jtag_req_t rv_jtag_o,
  input jtag_pkg::jtag_rsp_t rv_jtag_i,
  output jtag_pkg::jtag_req_t dft_jtag_o,
  input jtag_pkg::jtag_rsp_t dft_jtag_i,
  input  usb_out_of_rst_i,
  input  usb_aon_wake_en_i,
  input  usb_aon_wake_ack_i,
  input  usb_suspend_i,
  output usbdev_pkg::awk_state_t usb_state_debug_o,
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
  input prim_alert_pkg::alert_rx_t[NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t[NumAlerts-1:0] alert_tx_o,
  input [NMioPeriphOut-1:0] periph_to_mio_i,
  input [NMioPeriphOut-1:0] periph_to_mio_oe_i,
  output logic[NMioPeriphIn-1:0] mio_to_periph_o,
  input [NDioPads-1:0] periph_to_dio_i,
  input [NDioPads-1:0] periph_to_dio_oe_i,
  output logic[NDioPads-1:0] dio_to_periph_o,
  output prim_pad_wrapper_pkg::pad_attr_t[NMioPads-1:0] mio_attr_o,
  output logic[NMioPads-1:0] mio_out_o,
  output logic[NMioPads-1:0] mio_oe_o,
  input [NMioPads-1:0] mio_in_i,
  output prim_pad_wrapper_pkg::pad_attr_t[NDioPads-1:0] dio_attr_o,
  output logic[NDioPads-1:0] dio_out_o,
  output logic[NDioPads-1:0] dio_oe_o,
  input [NDioPads-1:0] dio_in_i
);


  pinmux #(
    .TargetCfg(TargetCfg),
    .AlertAsyncOn(AlertAsyncOn)
  ) dut (
    .clk_i,
    .rst_ni,
    .scanmode_i,
    .clk_aon_i,
    .rst_aon_ni,
    .pin_wkup_req_o,
    .usb_wkup_req_o,
    .sleep_en_i,
    .strap_en_i,
    .lc_dft_en_i,
    .lc_hw_debug_en_i,
    .dft_strap_test_o,
    .dft_hold_tap_sel_i,
    .lc_jtag_o,
    .lc_jtag_i,
    .rv_jtag_o,
    .rv_jtag_i,
    .dft_jtag_o,
    .dft_jtag_i,
    .usb_out_of_rst_i,
    .usb_aon_wake_en_i,
    .usb_aon_wake_ack_i,
    .usb_suspend_i,
    .usb_state_debug_o,
    .tl_i,
    .tl_o,
    .alert_rx_i,
    .alert_tx_o,
    .periph_to_mio_i,
    .periph_to_mio_oe_i,
    .mio_to_periph_o,
    .periph_to_dio_i,
    .periph_to_dio_oe_i,
    .dio_to_periph_o,
    .mio_attr_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i,
    .dio_attr_o,
    .dio_out_o,
    .dio_oe_o,
    .dio_in_i
  );


endmodule : pinmux_tb
