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
  logic [$clog2(pinmux_reg_pkg::NMioPads)-1:0] mio_sel_i;
  logic [$clog2(pinmux_reg_pkg::NDioPads)-1:0] dio_sel_i;
  logic [$clog2(pinmux_reg_pkg::NWkupDetect)-1:0] wkup_sel_i;

  `ASSUME(PeriphSelRange_M, periph_sel_i < pinmux_reg_pkg::NMioPeriphIn)
  `ASSUME(PeriphSelStable_M, ##1 $stable(periph_sel_i))

  `ASSUME(MioSelRange_M, mio_sel_i < pinmux_reg_pkg::NMioPads && !(mio_sel_i inside
          {TargetCfg.tck_idx, TargetCfg.tms_idx, TargetCfg.trst_idx, TargetCfg.tdi_idx,
           TargetCfg.tdo_idx}))
  `ASSUME(MioSelStable_M, ##1 $stable(mio_sel_i))

  `ASSUME(DioSelRange_M, dio_sel_i < pinmux_reg_pkg::NDioPads)
  `ASSUME(DioSelStable_M, ##1 $stable(dio_sel_i))

  `ASSUME(WkupSelRange_M, wkup_sel_i < pinmux_reg_pkg::NWkupDetect)
  `ASSUME(WkupSelStable_M, ##1 $stable(wkup_sel_i))

  // ------ Input mux assertions ------
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

  `ASSERT(DioInSelN_A, dio_to_periph_o == dio_in_i)

  // ------ Output mux assertions ------
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

  // ------ Mio sleep behavior assertions ------
  pinmux_reg_pkg::pinmux_reg2hw_mio_pad_sleep_en_mreg_t mio_pad_sleep_en;
  assign mio_pad_sleep_en = pinmux.reg2hw.mio_pad_sleep_en[mio_sel_i];
  pinmux_reg_pkg::pinmux_reg2hw_mio_pad_sleep_mode_mreg_t mio_pad_sleep_mode;
  assign mio_pad_sleep_mode = pinmux.reg2hw.mio_pad_sleep_mode[mio_sel_i];

  `ASSERT(MioSleepMode0_A, ##1 mio_pad_sleep_mode.q == 0 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          mio_out_o[mio_sel_i] == 1'b0)
  `ASSERT(MioSleepMode1_A, ##1 mio_pad_sleep_mode.q == 1 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          mio_out_o[mio_sel_i] == 1'b1)
  `ASSERT(MioSleepMode2_A, ##1 mio_pad_sleep_mode.q == 2 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          mio_out_o[mio_sel_i] == 1'b0)
  `ASSERT(MioSleepMode3_A, ##1 mio_pad_sleep_mode.q == 3 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          $stable(mio_out_o[mio_sel_i]))
  `ASSERT(MioSleepStable_A, ##1 !$rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          $stable(mio_out_o[mio_sel_i]))

  `ASSERT(MioOeSleepMode0_A, ##1 mio_pad_sleep_mode.q == 0 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q && sleep_en_i|->
          mio_oe_o[mio_sel_i] == 1'b1)
  `ASSERT(MioOeSleepMode1_A, ##1 mio_pad_sleep_mode.q == 1 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          mio_oe_o[mio_sel_i] == 1'b1)
  `ASSERT(MioOeSleepMode2_A, ##1 mio_pad_sleep_mode.q == 2 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          mio_oe_o[mio_sel_i] == 1'b0)
  `ASSERT(MioOeSleepMode3_A, ##1 mio_pad_sleep_mode.q == 3 && mio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          $stable(mio_oe_o[mio_sel_i]))
  `ASSERT(MioOeSleepStable_A, ##1 !$rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 mio_pad_sleep_status.q |->
          $stable(mio_oe_o[mio_sel_i]))

  // ------ Mio_attr_o ------
  pinmux_reg_pkg::pinmux_reg2hw_mio_pad_attr_mreg_t mio_pad_attr;
  assign mio_pad_attr = pinmux.mio_pad_attr_q[mio_sel_i];

  pad_attr_t mio_pad_attr_mask;
  pad_type_e bid_pad_types[4] = {BidirStd, BidirTol, DualBidirTol, BidirOd};
  assign mio_pad_attr_mask.invert = TargetCfg.mio_pad_type[mio_sel_i] == AnalogIn0 ? 0 : 1;
  assign mio_pad_attr_mask.virt_od_en = TargetCfg.mio_pad_type[mio_sel_i] inside {bid_pad_types} ?
                                        1 : 0;
  assign mio_pad_attr_mask.pull_en = TargetCfg.mio_pad_type[mio_sel_i] == AnalogIn0 ? 0 : 1;
  assign mio_pad_attr_mask.pull_select = TargetCfg.mio_pad_type[mio_sel_i] == AnalogIn0 ? 0 : 1;
  assign mio_pad_attr_mask.keep_en = TargetCfg.mio_pad_type[mio_sel_i] inside {bid_pad_types} ?
                                     1 : 0;
  assign mio_pad_attr_mask.drive_strength[0] = TargetCfg.mio_pad_type[mio_sel_i] inside
                                               {bid_pad_types} ? 1 : 0;
  assign mio_pad_attr_mask.schmitt_en = 0;
  assign mio_pad_attr_mask.od_en = 0;
  assign mio_pad_attr_mask.slew_rate = '0;
  assign mio_pad_attr_mask.drive_strength[3:1] = '0;

  `ASSERT(MioAttrO_A, mio_attr_o[mio_sel_i] == (mio_pad_attr & mio_pad_attr_mask))

  // ------ Dio_attr_o ------
  pinmux_reg_pkg::pinmux_reg2hw_dio_pad_attr_mreg_t dio_pad_attr;
  assign dio_pad_attr = pinmux.dio_pad_attr_q[dio_sel_i];

  pad_attr_t dio_pad_attr_mask;
  assign dio_pad_attr_mask.invert = TargetCfg.dio_pad_type[dio_sel_i] == AnalogIn0 ? 0 : 1;
  assign dio_pad_attr_mask.virt_od_en = TargetCfg.dio_pad_type[dio_sel_i] inside {bid_pad_types} ?
                                        1 : 0;
  assign dio_pad_attr_mask.pull_en = TargetCfg.dio_pad_type[dio_sel_i] == AnalogIn0 ? 0 : 1;
  assign dio_pad_attr_mask.pull_select = TargetCfg.dio_pad_type[dio_sel_i] == AnalogIn0 ? 0 : 1;
  assign dio_pad_attr_mask.keep_en     = TargetCfg.dio_pad_type[dio_sel_i] inside {bid_pad_types} ?
                                         1 : 0;
  assign dio_pad_attr_mask.drive_strength[0] = TargetCfg.dio_pad_type[dio_sel_i] inside
                                               {bid_pad_types} ? 1 : 0;
  assign dio_pad_attr_mask.schmitt_en = 0;
  assign dio_pad_attr_mask.od_en = 0;
  assign dio_pad_attr_mask.slew_rate = '0;
  assign dio_pad_attr_mask.drive_strength[3:1] = '0;

  `ASSERT(DioAttrO_A, dio_attr_o[dio_sel_i] == (dio_pad_attr & dio_pad_attr_mask))

  // ------ Output dedicated output assertions ------
  pinmux_reg_pkg::pinmux_reg2hw_dio_pad_sleep_status_mreg_t dio_pad_sleep_status;
  assign dio_pad_sleep_status = pinmux.reg2hw.dio_pad_sleep_status[dio_sel_i];

  `ASSERT(DOutSelN_A, !dio_pad_sleep_status.q |->
          dio_out_o[dio_sel_i] == periph_to_dio_i[dio_sel_i])

  `ASSERT(DOutSelOeN_A, !dio_pad_sleep_status.q |->
          dio_oe_o[dio_sel_i] == periph_to_dio_oe_i[dio_sel_i])

  // ------ Dio sleep behavior assertions ------
  pinmux_reg_pkg::pinmux_reg2hw_dio_pad_sleep_en_mreg_t dio_pad_sleep_en;
  assign dio_pad_sleep_en = pinmux.reg2hw.dio_pad_sleep_en[dio_sel_i];
  pinmux_reg_pkg::pinmux_reg2hw_dio_pad_sleep_mode_mreg_t dio_pad_sleep_mode;
  assign dio_pad_sleep_mode = pinmux.reg2hw.dio_pad_sleep_mode[dio_sel_i];

  `ASSERT(DioSleepMode0_A, ##1 dio_pad_sleep_mode.q == 0 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          dio_out_o[dio_sel_i] == 1'b0)
  `ASSERT(DioSleepMode1_A, ##1 dio_pad_sleep_mode.q == 1 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          dio_out_o[dio_sel_i] == 1'b1)
  `ASSERT(DioSleepMode2_A, ##1 dio_pad_sleep_mode.q == 2 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          dio_out_o[dio_sel_i] == 1'b0)
  `ASSERT(DioSleepMode3_A, ##1 dio_pad_sleep_mode.q == 3 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          $stable(dio_out_o[dio_sel_i]))
  `ASSERT(DioSleepStable_A, ##1 !$rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          $stable(dio_out_o[dio_sel_i]))

  `ASSERT(DioOeSleepMode0_A, ##1 dio_pad_sleep_mode.q == 0 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          dio_oe_o[dio_sel_i] == 1'b1)
  `ASSERT(DioOeSleepMode1_A, ##1 dio_pad_sleep_mode.q == 1 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          dio_oe_o[dio_sel_i] == 1'b1)
  `ASSERT(DioOeSleepMode2_A, ##1 dio_pad_sleep_mode.q == 2 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          dio_oe_o[dio_sel_i] == 1'b0)
  `ASSERT(DioOeSleepMode3_A, ##1 dio_pad_sleep_mode.q == 3 && dio_pad_sleep_en.q == 1 &&
          $rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          $stable(dio_oe_o[dio_sel_i]))
  `ASSERT(DioOeSleepStable_A, ##1 !$rose(sleep_en_i)
          // Ensure SW does not write to sleep status register to clear sleep status.
          ##1 dio_pad_sleep_status.q |->
          $stable(dio_oe_o[dio_sel_i]))

  // ------Dio backward assertions ------
  `ASSERT(Dio0Backward_A, dio_out_o[dio_sel_i] == 0 |->
          // Input is 0.
          periph_to_dio_i[dio_sel_i] == 0 ||
          // Sleep mode set to 0 and 2.
          $past(dio_pad_sleep_mode.q) inside {0, 2} ||
          // Previous value is 0 and sleep mode is set to 3.
          ($past(dio_out_o[dio_sel_i]) == 0) &&
           ($past(dio_pad_sleep_mode.q) == 3 ||
            // Previous value is 0 and sleep mode selection is disabled either by sleep_en_i input
            // or sleep_en CSR.
            ($past(!$rose(sleep_en_i) || !dio_pad_sleep_en.q) && dio_pad_sleep_status.q)))

  `ASSERT(Dio1Backward_A, dio_out_o[dio_sel_i] == 1 |->
          // input is 1.
          periph_to_dio_i[dio_sel_i] == 1 ||
          // Sleep mode set to 1.
          $past(dio_pad_sleep_mode.q) == 1 ||
          // Previous value is 1 and sleep mode is set to 3.
          ($past(dio_out_o[dio_sel_i]) == 1) &&
           ($past(dio_pad_sleep_mode.q) == 3 ||
            // Previous value is 1 and sleep mode selection is disabled either by sleep_en_i input
            // or sleep_en CSR.
            ($past(!$rose(sleep_en_i) || !dio_pad_sleep_en.q) && dio_pad_sleep_status.q)))

  `ASSERT(DioOe0Backward_A, dio_oe_o[dio_sel_i] == 0 |->
          // Input is 0.
          periph_to_dio_oe_i[dio_sel_i] == 0 ||
          // Sleep mode set to 2.
          $past(dio_pad_sleep_mode.q) == 2 ||
          // Previous value is 0 and sleep mode is set to 3.
          ($past(dio_oe_o[dio_sel_i]) == 0) &&
           ($past(dio_pad_sleep_mode.q) == 3 ||
            // Previous value is 0 and sleep mode selection is disabled either by sleep_en_i input
            // or sleep_en CSR.
            ($past(!$rose(sleep_en_i) || !dio_pad_sleep_en.q) && dio_pad_sleep_status.q)))

  `ASSERT(DioOe1Backward_A, dio_oe_o[dio_sel_i] == 1 |->
          // input is 1.
          periph_to_dio_oe_i[dio_sel_i] == 1 ||
          // Sleep mode set to 0 or 1.
          $past(dio_pad_sleep_mode.q) inside {0, 1} ||
          // Previous value is 1 and sleep mode is set to 3.
          ($past(dio_oe_o[dio_sel_i]) == 1) &&
           ($past(dio_pad_sleep_mode.q) == 3 ||
            // Previous value is 1 and sleep mode selection is disabled either by sleep_en_i input
            // or sleep_en CSR.
            ($past(!$rose(sleep_en_i) || !dio_pad_sleep_en.q) && dio_pad_sleep_status.q)))

  // ------ Wakeup assertions ------
  pinmux_reg2hw_wkup_detector_en_mreg_t wkup_detector_en;
  assign wkup_detector_en = pinmux.reg2hw.wkup_detector_en[wkup_sel_i];
  pinmux_reg2hw_wkup_detector_mreg_t wkup_detector;
  assign wkup_detector = pinmux.reg2hw.wkup_detector[wkup_sel_i];
  pinmux_reg2hw_wkup_detector_cnt_th_mreg_t wkup_detector_cnt_th;
  assign wkup_detector_cnt_th = pinmux.reg2hw.wkup_detector_cnt_th[wkup_sel_i];
  pinmux_reg2hw_wkup_detector_padsel_mreg_t wkup_detector_padsel;
  assign wkup_detector_padsel = pinmux.reg2hw.wkup_detector_padsel[wkup_sel_i];
  pinmux_hw2reg_wkup_cause_mreg_t wkup_cause;
  assign wkup_cause = pinmux.hw2reg.wkup_cause[wkup_sel_i];
  pinmux_reg2hw_wkup_cause_mreg_t wkup_cause_reg2hw;

  // Variable to gether all wkup causes.
  assign wkup_cause_reg2hw = pinmux.reg2hw.wkup_cause[wkup_sel_i];
  logic[pinmux_reg_pkg::NWkupDetect-1:0]  wkup_cause_q;
  for (genvar i = 0; i < pinmux_reg_pkg::NWkupDetect; i++) begin : gen_wkup_cause_q
    assign wkup_cause_q[i] = pinmux.reg2hw.wkup_cause[i].q;
  end

  // Retrieve pin value based on Mio and Dio selection.
  logic pin_val;
  assign pin_val = wkup_detector.miodio.q ?
                   (wkup_detector_padsel.q >= pinmux_reg_pkg::NDioPads ? 0 :
                    dio_in_i[wkup_detector_padsel.q]) :
                   (wkup_detector_padsel.q >= (pinmux_reg_pkg::NMioPads + 2) ? 0 :
                    wkup_detector_padsel == 0 ? 0 :
                    wkup_detector_padsel == 1 ? 1 :
                    mio_in_i[wkup_detector_padsel.q - 2]);

  // Retrieve filterd pin value with a 2 aon_clock synchronizer.
  logic [3:0] filter_vals;
  logic pin_val_sync_1, pin_val_sync_2;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
     if (!rst_aon_ni) begin
       pin_val_sync_1 <= 1'b0;
       pin_val_sync_2 <= 1'b0;
      end else begin
        pin_val_sync_1 <= pin_val;
        pin_val_sync_2 <= pin_val_sync_1;
      end
  end

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      filter_vals <= 4'b0;
    end else if (pin_val_sync_2 == filter_vals[0]) begin
      filter_vals <= (filter_vals << 1) | pin_val_sync_2;
    end else begin
      filter_vals <= {filter_vals[3], filter_vals[3], filter_vals[3], pin_val_sync_2};
    end
  end

  logic final_pin_val = wkup_detector.filter.q ? filter_vals[3] : pin_val_sync_2;

  // Threshold counters.
  // Adding one more bit for the counters to check overflow case.
  bit [WkupCntWidth:0] high_cnter, low_cnter;
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni || !wkup_detector_en.q) begin
      high_cnter <= 0;
      low_cnter  <= 0;
    end else if (wkup_detector.mode.q == 3) begin
      low_cnter <= 0;
      if (final_pin_val && (high_cnter < wkup_detector_cnt_th.q)) begin
        high_cnter <= high_cnter + 1;
      end else begin
        high_cnter <= 0;
      end
    end else if (wkup_detector.mode.q == 4) begin
      high_cnter  <= 0;
      if (!final_pin_val && (low_cnter < wkup_detector_cnt_th.q)) begin
        low_cnter <= low_cnter + 1;
      end else begin
        low_cnter <= 0;
      end
    end else begin
      high_cnter <= 0;
      low_cnter  <= 0;
    end
  end

  `ASSERT(WkupPosedge_A, wkup_detector_en.q && wkup_detector.mode.q == 0 &&
          $rose(final_pin_val) |-> wkup_cause.de,
          clk_aon_i, !rst_aon_ni)
  `ASSERT(WkupNegedge_A, wkup_detector_en.q && wkup_detector.mode.q == 1 &&
          $fell(final_pin_val) |-> wkup_cause.de,
          clk_aon_i, !rst_aon_ni)
  `ASSERT(WkupEdge_A, wkup_detector_en.q && wkup_detector.mode.q == 2 &&
          ($fell(final_pin_val) || $rose(final_pin_val)) |-> wkup_cause.de,
          clk_aon_i, !rst_aon_ni)
  // TODO(#11194): The two assertions below will have cex.
  `ASSERT(WkupTimedHigh_A, (high_cnter >= wkup_detector_cnt_th.q) && wkup_detector_en.q &&
          wkup_detector.mode.q == 3 |-> wkup_cause.de,
          clk_aon_i, !rst_aon_ni)
  `ASSERT(WkupTimedLow_A, (low_cnter >= wkup_detector_cnt_th.q) && wkup_detector_en.q &&
          wkup_detector.mode.q == 4 |-> wkup_cause.de,
          clk_aon_i, !rst_aon_ni)

  `ASSERT(WkupCauseQ_A, wkup_cause.de && !u_reg.aon_wkup_cause_we |=>
          wkup_cause_reg2hw.q, clk_aon_i, !rst_aon_ni)

  `ASSERT(AonWkupO_A, |wkup_cause_q <-> pin_wkup_req_o, clk_aon_i, !rst_aon_ni)

  `ASSERT(WkupCause0_A, wkup_cause.de == 0 |->
          (wkup_detector_en.q == 0) ||
          (wkup_detector_en.q == 1 &&
           ((wkup_detector.mode.q == 0 && !$rose(final_pin_val)) ||
            (wkup_detector.mode.q > 4 && !$rose(final_pin_val)) ||
            (wkup_detector.mode.q == 1 && !$fell(final_pin_val)) ||
            (wkup_detector.mode.q == 2 && !$changed(final_pin_val)) ||
            (wkup_detector.mode.q == 3 && (high_cnter < wkup_detector_cnt_th.q)) ||
            (wkup_detector.mode.q == 4 && (low_cnter < wkup_detector_cnt_th.q)))),
          clk_aon_i, !rst_aon_ni)

  `ASSERT(WkupCause1_A, wkup_cause.de == 1 |->
          wkup_detector_en.q == 1 &&
           ((wkup_detector.mode.q == 0 && $rose(final_pin_val)) ||
            (wkup_detector.mode.q > 4 && $rose(final_pin_val)) ||
            (wkup_detector.mode.q == 1 && $fell(final_pin_val)) ||
            (wkup_detector.mode.q == 2 && $changed(final_pin_val)) ||
            (wkup_detector.mode.q == 3 && (high_cnter >= wkup_detector_cnt_th.q)) ||
            (wkup_detector.mode.q == 4 && (low_cnter >= wkup_detector_cnt_th.q))),
          clk_aon_i, !rst_aon_ni)

  // ------ JTAG pinmux input assertions ------
  `ASSERT(LcJtagOWoScanmode_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::LcTapSel &&
          !prim_mubi_pkg::mubi4_test_true_strict(scanmode_i) |->
          lc_jtag_o == {mio_in_i[TargetCfg.tck_idx],
                        mio_in_i[TargetCfg.tms_idx],
                        mio_in_i[TargetCfg.trst_idx],
                        mio_in_i[TargetCfg.tdi_idx]})
  `ASSERT(LcJtagOWScanmode_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::LcTapSel &&
          prim_mubi_pkg::mubi4_test_true_strict(scanmode_i) |->
          lc_jtag_o == {mio_in_i[TargetCfg.tck_idx],
                        mio_in_i[TargetCfg.tms_idx],
                        rst_ni,
                        mio_in_i[TargetCfg.tdi_idx]})
  `ASSERT(LcJtagOStable_A, u_pinmux_strap_sampling.tap_strap != pinmux_pkg::LcTapSel &&
          $past(u_pinmux_strap_sampling.tap_strap) != pinmux_pkg::LcTapSel |->
          $stable(lc_jtag_o))
  `ASSERT(LcJtagODefault_A, u_pinmux_strap_sampling.tap_strap != pinmux_pkg::LcTapSel |->
          lc_jtag_o == '0)

  // Lc_hw_debug_en_i signal goes through a two clock cycle synchronizer.
  `ASSERT(RvJtagOWoScanmode_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::RvTapSel &&
          !prim_mubi_pkg::mubi4_test_true_strict(scanmode_i) &&
          $past(lc_hw_debug_en_i, 2) == lc_ctrl_pkg::On |->
          rv_jtag_o == {mio_in_i[TargetCfg.tck_idx],
                        mio_in_i[TargetCfg.tms_idx],
                        mio_in_i[TargetCfg.trst_idx],
                        mio_in_i[TargetCfg.tdi_idx]})
  `ASSERT(RvJtagOWScanmode_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::RvTapSel &&
          prim_mubi_pkg::mubi4_test_true_strict(scanmode_i) &&
          $past(lc_hw_debug_en_i, 2) == lc_ctrl_pkg::On |->
          rv_jtag_o == {mio_in_i[TargetCfg.tck_idx],
                        mio_in_i[TargetCfg.tms_idx],
                        rst_ni,
                        mio_in_i[TargetCfg.tdi_idx]})
  `ASSERT(RvJtagOStable_A, (u_pinmux_strap_sampling.tap_strap != pinmux_pkg::RvTapSel &&
          $past(u_pinmux_strap_sampling.tap_strap) != pinmux_pkg::RvTapSel) ||
          ($past(lc_hw_debug_en_i, 2) != lc_ctrl_pkg::On &&
           $past(lc_hw_debug_en_i, 3) != lc_ctrl_pkg::On) |->
          $stable(rv_jtag_o))
  `ASSERT(RvJtagODefault_A, u_pinmux_strap_sampling.tap_strap != pinmux_pkg::RvTapSel ||
          $past(lc_hw_debug_en_i, 2) != lc_ctrl_pkg::On |->
          rv_jtag_o == '0)

  // Lc_dft_en_i signal goes through a two clock cycle synchronizer.
  `ASSERT(DftJtagOWoScanmode_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::DftTapSel &&
          !prim_mubi_pkg::mubi4_test_true_strict(scanmode_i) &&
          $past(lc_dft_en_i, 2) == lc_ctrl_pkg::On |->
          dft_jtag_o == {mio_in_i[TargetCfg.tck_idx],
                         mio_in_i[TargetCfg.tms_idx],
                         mio_in_i[TargetCfg.trst_idx],
                         mio_in_i[TargetCfg.tdi_idx]})
  `ASSERT(DftJtagOWScanmode_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::DftTapSel &&
          prim_mubi_pkg::mubi4_test_true_strict(scanmode_i) &&
          $past(lc_dft_en_i, 2) == lc_ctrl_pkg::On |->
          dft_jtag_o == {mio_in_i[TargetCfg.tck_idx],
                         mio_in_i[TargetCfg.tms_idx],
                         rst_ni,
                         mio_in_i[TargetCfg.tdi_idx]})
  `ASSERT(DftJtagOStable_A, (u_pinmux_strap_sampling.tap_strap != pinmux_pkg::DftTapSel &&
          $past(u_pinmux_strap_sampling.tap_strap) != pinmux_pkg::DftTapSel) ||
          ($past(lc_dft_en_i, 2) != lc_ctrl_pkg::On &&
           $past(lc_dft_en_i, 3) != lc_ctrl_pkg::On) |->
          $stable(dft_jtag_o))
  `ASSERT(DftJtagODefault_A, u_pinmux_strap_sampling.tap_strap != pinmux_pkg::DftTapSel ||
          $past(lc_dft_en_i, 2) != lc_ctrl_pkg::On |->
          dft_jtag_o == '0)

  `ASSERT(TapStrap_A, ##2 ((!dft_hold_tap_sel_i && $past(lc_dft_en_i, 2) == lc_ctrl_pkg::On) ||
          strap_en_i) && $past(lc_hw_debug_en_i, 2) == lc_ctrl_pkg::On |=>
          u_pinmux_strap_sampling.tap_strap ==
          $past({mio_in_i[TargetCfg.tap_strap1_idx], mio_in_i[TargetCfg.tap_strap0_idx]}))

  `ASSERT(TapStrap0_A, ##2 ((!dft_hold_tap_sel_i && $past(lc_dft_en_i, 2) == lc_ctrl_pkg::On) ||
          strap_en_i) |=>
          u_pinmux_strap_sampling.tap_strap[0] == $past(mio_in_i[TargetCfg.tap_strap0_idx]))

  `ASSERT(TapStrapStable_A, dft_hold_tap_sel_i && !strap_en_i |=>
          $stable(u_pinmux_strap_sampling.tap_strap))

  // ------ JTAG pinmux output assertions ------
  `ASSERT(LcJtagI_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::LcTapSel |->
          lc_jtag_i == {mio_out_o[TargetCfg.tdo_idx],
                        mio_oe_o[TargetCfg.tdo_idx]})
  `ASSERT(RvJtagI_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::RvTapSel &&
          $past(lc_hw_debug_en_i, 2) == lc_ctrl_pkg::On |->
          rv_jtag_i == {mio_out_o[TargetCfg.tdo_idx],
                        mio_oe_o[TargetCfg.tdo_idx]})
  `ASSERT(DftJtagI_A, u_pinmux_strap_sampling.tap_strap == pinmux_pkg::DftTapSel &&
          $past(lc_dft_en_i, 2) == lc_ctrl_pkg::On |->
          dft_jtag_i == {mio_out_o[TargetCfg.tdo_idx],
                        mio_oe_o[TargetCfg.tdo_idx]})

  // ------ DFT strap_test_o assertions ------
  `ASSERT(DftStrapTestO_A, ##2 strap_en_i &&
          $past(lc_dft_en_i, 2) == lc_ctrl_pkg::On |=>
          dft_strap_test_o.valid &&
          dft_strap_test_o.straps == $past({mio_in_i[TargetCfg.dft_strap1_idx],
                                            mio_in_i[TargetCfg.dft_strap0_idx]}))
  `ASSERT(DftStrapTestOValidStable_A, dft_strap_test_o.valid |=> dft_strap_test_o.valid)
  `ASSERT(DftStrapTestOStrapStable_A, dft_strap_test_o.valid |->
          $stable(dft_strap_test_o.straps) ||
          (dft_strap_test_o.straps == $past({mio_in_i[TargetCfg.dft_strap1_idx],
                                             mio_in_i[TargetCfg.dft_strap0_idx]})))

endmodule : pinmux_assert_fpv
