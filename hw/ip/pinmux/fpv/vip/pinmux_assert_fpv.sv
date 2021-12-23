// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for pinmux.
// Intended to be used with a formal tool.

`include "prim_assert.sv"

module pinmux_assert_fpv
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
  input logic pin_wkup_req_o,
  input logic usb_wkup_req_o,
  input  sleep_en_i,
  input  strap_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input dft_strap_test_req_t dft_strap_test_o,
  input  dft_hold_tap_sel_i,
  input jtag_pkg::jtag_req_t lc_jtag_o,
  input jtag_pkg::jtag_rsp_t lc_jtag_i,
  input jtag_pkg::jtag_req_t rv_jtag_o,
  input jtag_pkg::jtag_rsp_t rv_jtag_i,
  input jtag_pkg::jtag_req_t dft_jtag_o,
  input jtag_pkg::jtag_rsp_t dft_jtag_i,
  input  usb_out_of_rst_i,
  input  usb_aon_wake_en_i,
  input  usb_aon_wake_ack_i,
  input  usb_suspend_i,
  input usbdev_pkg::awk_state_t usb_state_debug_o,
  input tlul_pkg::tl_h2d_t tl_i,
  input tlul_pkg::tl_d2h_t tl_o,
  input prim_alert_pkg::alert_rx_t[NumAlerts-1:0] alert_rx_i,
  input prim_alert_pkg::alert_tx_t[NumAlerts-1:0] alert_tx_o,
  input [NMioPeriphOut-1:0] periph_to_mio_i,
  input [NMioPeriphOut-1:0] periph_to_mio_oe_i,
  input logic[NMioPeriphIn-1:0] mio_to_periph_o,
  input [NDioPads-1:0] periph_to_dio_i,
  input [NDioPads-1:0] periph_to_dio_oe_i,
  input logic[NDioPads-1:0] dio_to_periph_o,
  input prim_pad_wrapper_pkg::pad_attr_t[NMioPads-1:0] mio_attr_o,
  input logic[NMioPads-1:0] mio_out_o,
  input logic[NMioPads-1:0] mio_oe_o,
  input [NMioPads-1:0] mio_in_i,
  input prim_pad_wrapper_pkg::pad_attr_t[NDioPads-1:0] dio_attr_o,
  input logic[NDioPads-1:0] dio_out_o,
  input logic[NDioPads-1:0] dio_oe_o,
  input [NDioPads-1:0] dio_in_i
);

  ///////////////////////////////
  // Declarations & Parameters //
  ///////////////////////////////

  /////////////////
  // Assumptions //
  /////////////////

  // Symbolic inputs for FPV
  logic [$clog2(pinmux_reg_pkg::NMioPeriphIn)-1:0] periph_sel_i;
  logic [$clog2(pinmux_reg_pkg::NMioPads)-1:0]  mio_sel_i;

  `ASSUME(PeriphSelRange_M, periph_sel_i < pinmux_reg_pkg::NMioPeriphIn)
  `ASSUME(PeriphSelStable_M, ##1 $stable(periph_sel_i))

  `ASSUME(MioSelRange_M, mio_sel_i < pinmux_reg_pkg::NMioPads && mio_sel_i != TargetCfg.tdo_idx)
  `ASSUME(MioSelStable_M, ##1 $stable(mio_sel_i))

  // Input mux assertions
  pinmux_reg_pkg::pinmux_reg2hw_mio_periph_insel_mreg_t periph_insel;
  assign periph_insel = pinmux.reg2hw.mio_periph_insel[periph_sel_i];

  `ASSERT(InSel0_A, periph_insel.q == 0 |-> mio_to_periph_o[periph_sel_i] == 1'b0)
  `ASSERT(InSel1_A, periph_insel.q == 1 |-> mio_to_periph_o[periph_sel_i] == 1'b1)
  `ASSERT(InSelN_A, periph_insel.q > 1 && periph_insel.q < (pinmux_reg_pkg::NMioPads + 2) &&
          !((periph_insel.q - 2) inside {TargetCfg.tck_idx, TargetCfg.tms_idx, TargetCfg.trst_idx,
                                         TargetCfg.tdi_idx, TargetCfg.tdo_idx}) |->
          mio_to_periph_o[periph_sel_i] == mio_in_i[periph_insel.q - 2])
   `ASSERT(InSelOOB_A, periph_insel.q >= (pinmux_reg_pkg::NMioPads + 2) |->
          mio_to_periph_o[periph_sel_i] == 0)
  // TODO: fix and uncomment the assertion below
  //`ASSERT(MioToPeriphO_A, ##1 !$stable(mio_to_periph_o[periph_sel_i]) |->
  //        !$stable(mio_in_i[periph_insel.q - 2]) || !$stable(periph_insel.q))

  //Output mux assertions
  pinmux_reg_pkg::pinmux_reg2hw_mio_outsel_mreg_t mio_outsel;
  assign mio_outsel = pinmux.reg2hw.mio_outsel[mio_sel_i];

  pinmux_reg_pkg::pinmux_reg2hw_mio_pad_sleep_status_mreg_t mio_pad_sleep_status;
  assign mio_pad_sleep_status = pinmux.reg2hw.mio_pad_sleep_status[mio_sel_i];


  `ASSERT(OutSel0_A, mio_outsel.q == 0 && !mio_pad_sleep_status.q |-> mio_out_o[mio_sel_i] == 1'b0)
  `ASSERT(OutSel1_A, mio_outsel.q == 1 && !mio_pad_sleep_status.q |-> mio_out_o[mio_sel_i] == 1'b1)
  `ASSERT(OutSel2_A, mio_outsel.q == 2 && !mio_pad_sleep_status.q |-> mio_out_o[mio_sel_i] == 1'b0)
  `ASSERT(OutSelN_A, mio_outsel.q > 2 && mio_outsel.q < (pinmux_reg_pkg::NMioPeriphOut + 3) &&
          !mio_pad_sleep_status.q |-> mio_out_o[mio_sel_i] == periph_to_mio_i[mio_outsel.q - 3])
  `ASSERT(OutSelOOB_A, mio_outsel.q >= (pinmux_reg_pkg::NMioPeriphOut + 3) &&
          !mio_pad_sleep_status.q |-> mio_out_o[mio_sel_i] == 0)
  // TODO: fix and uncomment the assertion below
  //`ASSERT(MioOutO_A, ##1 !$stable(mio_out_o[mio_sel_i]) |->
  //        !$stable(mio_outsel.q) || !$stable(periph_to_mio_i[mio_outsel.q - 3]))

  `ASSERT(OutSelOe0_A, mio_outsel.q == 0 && !mio_pad_sleep_status.q |->
          mio_oe_o[mio_sel_i] == 1'b1)
  `ASSERT(OutSelOe1_A, mio_outsel.q == 1 && !mio_pad_sleep_status.q |->
          mio_oe_o[mio_sel_i] == 1'b1)
  `ASSERT(OutSelOe2_A, mio_outsel.q == 2 && !mio_pad_sleep_status.q |->
          mio_oe_o[mio_sel_i] == 1'b0)
  `ASSERT(OutSelOeN_A, mio_outsel.q > 2 && mio_outsel.q < (pinmux_reg_pkg::NMioPeriphOut + 3) &&
          !mio_pad_sleep_status.q |-> mio_oe_o[mio_sel_i] == periph_to_mio_oe_i[mio_outsel.q - 3])
  `ASSERT(OutSelOeOOB_A, mio_outsel.q >= (pinmux_reg_pkg::NMioPeriphOut + 3) &&
          !mio_pad_sleep_status.q |-> mio_oe_o[mio_sel_i] == 0)
  // TODO: fix and uncomment the assertion below
  //`ASSERT(MioOeO_A, ##1 !$stable(mio_oe_o[mio_sel_i]) |->
  //    !$stable(mio_outsel.q) || !$stable(periph_to_mio_oe_i[mio_outsel.q - 3]))
endmodule : pinmux_assert_fpv
