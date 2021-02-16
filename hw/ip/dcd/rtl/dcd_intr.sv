// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: DCD interrupt Module
//
module dcd_intr import dcd_reg_pkg::*; (
  input  clk_i,
  input  rst_ni,
  input  clk_aon_i,
  input  rst_slow_ni,

  input  [NumAdcFilter-1:0] cfg_wakeup_en,
  input  [NumAdcFilter-1:0] cfg_intr_en,
  input  cfg_oneshot_intr_en,
  input  [NumAdcFilter-1:0] dcd_match_pulse,
  input  cfg_oneshot_done,

  input  dcd_reg2hw_intr_state_reg_t intr_state_i,
  input  dcd_reg2hw_intr_enable_reg_t intr_enable_i,
  input  dcd_reg2hw_intr_test_reg_t intr_test_i,

  output dcd_hw2reg_intr_state_reg_t intr_state_o,
  output dcd_hw2reg_adc_intr_status_reg_t adc_intr_status_o,
  output dcd_hw2reg_adc_wakeup_status_reg_t adc_wakeup_status_o,

  output debug_cable_wakeup_o,
  output intr_debug_cable_o
);

  logic [NumAdcFilter-1:0] cfg_dcd_match_done;
  logic dcd_event;

  //Synchronize from 200KHz always-onclock to 24MHz cfg clock
  prim_pulse_sync i_cc_sink_det (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[0]),
    .dst_pulse_o (cfg_dcd_match_done[0])
  );

  prim_pulse_sync i_cc_1a5_sink_det (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[1]),
    .dst_pulse_o (cfg_dcd_match_done[1])
  );

  prim_pulse_sync i_cc_3a0_sink_det (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[2]),
    .dst_pulse_o (cfg_dcd_match_done[2])
  );

  prim_pulse_sync i_cc_src_det (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[3]),
    .dst_pulse_o (cfg_dcd_match_done[3])
  );

  prim_pulse_sync i_cc_1a5_src_det (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[4]),
    .dst_pulse_o (cfg_dcd_match_done[4])
  );

  prim_pulse_sync i_cc_src_det_flip (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[5]),
    .dst_pulse_o (cfg_dcd_match_done[5])
  );

  prim_pulse_sync i_cc_1a5_src_det_flip (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[6]),
    .dst_pulse_o (cfg_dcd_match_done[6])
  );

  prim_pulse_sync i_cc_discon (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_match_pulse[7]),
    .dst_pulse_o (cfg_dcd_match_done[7])
  );

  //To write into interrupt status register
  assign adc_intr_status_o.cc_sink_det.de = cfg_dcd_match_done[0];
  assign adc_intr_status_o.cc_1a5_sink_det.de = cfg_dcd_match_done[1];
  assign adc_intr_status_o.cc_3a0_sink_det.de = cfg_dcd_match_done[2];
  assign adc_intr_status_o.cc_src_det.de = cfg_dcd_match_done[3];
  assign adc_intr_status_o.cc_1a5_src_det.de = cfg_dcd_match_done[4];
  assign adc_intr_status_o.cc_src_det_flip.de = cfg_dcd_match_done[5];
  assign adc_intr_status_o.cc_1a5_src_det_flip.de = cfg_dcd_match_done[6];
  assign adc_intr_status_o.cc_discon.de = cfg_dcd_match_done[7];
  assign adc_intr_status_o.oneshot.de = cfg_oneshot_done;

  assign adc_intr_status_o.cc_sink_det.d = 1'b1;
  assign adc_intr_status_o.cc_1a5_sink_det.d = 1'b1;
  assign adc_intr_status_o.cc_3a0_sink_det.d = 1'b1;
  assign adc_intr_status_o.cc_src_det.d = 1'b1;
  assign adc_intr_status_o.cc_1a5_src_det.d = 1'b1;
  assign adc_intr_status_o.cc_src_det_flip.d = 1'b1;
  assign adc_intr_status_o.cc_1a5_src_det_flip.d = 1'b1;
  assign adc_intr_status_o.cc_discon.d = 1'b1;
  assign adc_intr_status_o.oneshot.d = 1'b1;

  //Qualify each bit with intr_en
  assign dcd_event = (|(cfg_dcd_match_done & cfg_intr_en)) ||
         (cfg_oneshot_done & cfg_oneshot_intr_en);

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(1)) i_dcd_intr_o (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .event_intr_i           (dcd_event),
    .reg2hw_intr_enable_q_i (intr_enable_i.q),
    .reg2hw_intr_test_q_i   (intr_test_i.q),
    .reg2hw_intr_test_qe_i  (intr_test_i.qe),
    .reg2hw_intr_state_q_i  (intr_state_i.q),
    .hw2reg_intr_state_de_o (intr_state_o.de),
    .hw2reg_intr_state_d_o  (intr_state_o.d),
    .intr_o                 (intr_debug_cable_o)
  );

  //To write into wakeup status register
  assign adc_wakeup_status_o.cc_sink_det.de = cfg_dcd_match_done[0];
  assign adc_wakeup_status_o.cc_1a5_sink_det.de = cfg_dcd_match_done[1];
  assign adc_wakeup_status_o.cc_3a0_sink_det.de = cfg_dcd_match_done[2];
  assign adc_wakeup_status_o.cc_src_det.de = cfg_dcd_match_done[3];
  assign adc_wakeup_status_o.cc_1a5_src_det.de = cfg_dcd_match_done[4];
  assign adc_wakeup_status_o.cc_src_det_flip.de = cfg_dcd_match_done[5];
  assign adc_wakeup_status_o.cc_1a5_src_det_flip.de = cfg_dcd_match_done[6];
  assign adc_wakeup_status_o.cc_discon.de = cfg_dcd_match_done[7];

  assign adc_wakeup_status_o.cc_sink_det.d = 1'b1;
  assign adc_wakeup_status_o.cc_1a5_sink_det.d = 1'b1;
  assign adc_wakeup_status_o.cc_3a0_sink_det.d = 1'b1;
  assign adc_wakeup_status_o.cc_src_det.d = 1'b1;
  assign adc_wakeup_status_o.cc_1a5_src_det.d = 1'b1;
  assign adc_wakeup_status_o.cc_src_det_flip.d = 1'b1;
  assign adc_wakeup_status_o.cc_1a5_src_det_flip.d = 1'b1;
  assign adc_wakeup_status_o.cc_discon.d = 1'b1;

  //Qualify each bit with wakeup_en
  assign debug_cable_wakeup_o = |(cfg_dcd_match_done & cfg_wakeup_en);

endmodule
