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
  parameter int Tap0PadIdx = 0,
  parameter int Tap1PadIdx = 1,
  parameter int Dft0PadIdx = 2,
  parameter int Dft1PadIdx = 3,
  parameter int TckPadIdx = 4,
  parameter int TmsPadIdx = 5,
  parameter int TrstNPadIdx = 6,
  parameter int TdiPadIdx = 7,
  parameter int TdoPadIdx = 8,
  parameter int DioUsbdevDp = 9,
  parameter int DioUsbdevDn = 10,
  parameter int MioInUsbdevSense = 11,
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
  input usbdev_dppullup_en_i,
  input usbdev_dnpullup_en_i,
  output usb_dppullup_en_o,
  output usb_dnpullup_en_o,
  input usbdev_suspend_req_i,
  input usbdev_wake_ack_i,
  output usbdev_bus_reset_o,
  output usbdev_sense_lost_o,
  output usbdev_wake_detect_active_o,
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

  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:           TckPadIdx,
    tms_idx:           TmsPadIdx,
    trst_idx:          TrstNPadIdx,
    tdi_idx:           TdiPadIdx,
    tdo_idx:           TdoPadIdx,
    tap_strap0_idx:    Tap0PadIdx,
    tap_strap1_idx:    Tap1PadIdx,
    dft_strap0_idx:    Dft0PadIdx,
    dft_strap1_idx:    Dft1PadIdx,
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevDp,
    usb_dn_idx:        DioUsbdevDn,
    usb_sense_idx:     MioInUsbdevSense,
    // Pad types for attribute WARL behavior
    dio_pad_type:      {NDioPads{BidirStd}},
    mio_pad_type:      {NMioPads{BidirStd}}
  };

  pinmux #(
    .TargetCfg(PinmuxTargetCfg),
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
    .usbdev_dppullup_en_i,
    .usbdev_dnpullup_en_i,
    .usb_dppullup_en_o,
    .usb_dnpullup_en_o,
    .usbdev_suspend_req_i,
    .usbdev_wake_ack_i,
    .usbdev_bus_reset_o,
    .usbdev_sense_lost_o,
    .usbdev_wake_detect_active_o,
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
