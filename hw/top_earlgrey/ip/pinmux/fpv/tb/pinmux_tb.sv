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
  import top_earlgrey_pkg::*;
#(
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
  input  usb_dppullup_en_upwr_i,
  input  usb_dnpullup_en_upwr_i,
  output usb_dppullup_en_o,
  output usb_dnpullup_en_o,
  input  usb_out_of_rst_i,
  input  usb_aon_wake_en_i,
  input  usb_aon_wake_ack_i,
  input  usb_suspend_i,
  output usb_bus_reset_o,
  output usb_sense_lost_o,
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
  import top_earlgrey_pkg::*;

  parameter int Tap0PadIdx = 30;
  parameter int Tap1PadIdx = 27;
  parameter int Dft0PadIdx = 25;
  parameter int Dft1PadIdx = 26;
  parameter int TckPadIdx = 38;
  parameter int TmsPadIdx = 35;
  parameter int TrstNPadIdx = 39;
  parameter int TdiPadIdx = 37;
  parameter int TdoPadIdx = 36;

  // Parameters for chip_earlgrey_asic.
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
    usb_dp_idx:        DioUsbdevUsbDp,
    usb_dn_idx:        DioUsbdevUsbDn,
    usb_sense_idx:     MioInUsbdevSense,
    // Pad types for attribute WARL behavior
    dio_pad_type: {
      BidirOd, // DIO sysrst_ctrl_aon_flash_wp_l
      BidirTol, // DIO usbdev_rx_enable
      BidirTol, // DIO usbdev_suspend
      BidirTol, // DIO usbdev_tx_mode_se
      BidirTol, // DIO usbdev_dn_pullup
      BidirTol, // DIO usbdev_dp_pullup
      BidirTol, // DIO usbdev_se0
      BidirStd, // DIO spi_host0_csb
      BidirStd, // DIO spi_host0_sck
      BidirTol, // DIO usbdev_sense
      InputStd, // DIO spi_device_csb
      InputStd, // DIO spi_device_sck
      BidirOd, // DIO sysrst_ctrl_aon_ec_rst_l
      BidirTol, // DIO usbdev_dn
      BidirTol, // DIO usbdev_dp
      BidirTol, // DIO usbdev_d
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd  // DIO spi_host0_sd
    },
    mio_pad_type: {
      BidirOd, // MIO Pad 46
      BidirOd, // MIO Pad 45
      BidirOd, // MIO Pad 44
      BidirOd, // MIO Pad 43
      BidirStd, // MIO Pad 42
      BidirStd, // MIO Pad 41
      BidirStd, // MIO Pad 40
      BidirStd, // MIO Pad 39
      BidirStd, // MIO Pad 38
      BidirStd, // MIO Pad 37
      BidirStd, // MIO Pad 36
      BidirStd, // MIO Pad 35
      BidirOd, // MIO Pad 34
      BidirOd, // MIO Pad 33
      BidirOd, // MIO Pad 32
      BidirStd, // MIO Pad 31
      BidirStd, // MIO Pad 30
      BidirStd, // MIO Pad 29
      BidirStd, // MIO Pad 28
      BidirStd, // MIO Pad 27
      BidirStd, // MIO Pad 26
      BidirStd, // MIO Pad 25
      BidirStd, // MIO Pad 24
      BidirStd, // MIO Pad 23
      BidirStd, // MIO Pad 22
      BidirOd, // MIO Pad 21
      BidirOd, // MIO Pad 20
      BidirOd, // MIO Pad 19
      BidirOd, // MIO Pad 18
      BidirStd, // MIO Pad 17
      BidirStd, // MIO Pad 16
      BidirStd, // MIO Pad 15
      BidirStd, // MIO Pad 14
      BidirStd, // MIO Pad 13
      BidirStd, // MIO Pad 12
      BidirStd, // MIO Pad 11
      BidirStd, // MIO Pad 10
      BidirStd, // MIO Pad 9
      BidirOd, // MIO Pad 8
      BidirOd, // MIO Pad 7
      BidirOd, // MIO Pad 6
      BidirStd, // MIO Pad 5
      BidirStd, // MIO Pad 4
      BidirStd, // MIO Pad 3
      BidirStd, // MIO Pad 2
      BidirStd, // MIO Pad 1
      BidirStd  // MIO Pad 0
    }
  };

  pinmux #(
    .TargetCfg(PinmuxTargetCfg),
    .AlertAsyncOn(AlertAsyncOn)
  ) dut_asic (
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
    .usb_dppullup_en_upwr_i,
    .usb_dnpullup_en_upwr_i,
    .usb_dppullup_en_o,
    .usb_dnpullup_en_o,
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
