// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: adc_ctrl interrupt Module
//
module adc_ctrl_intr import adc_ctrl_reg_pkg::*; (
  input  clk_aon_i,
  input  rst_aon_ni,
  input  clk_i,
  input  rst_ni,

  input  [NumAdcFilter-1:0] aon_filter_match_i,
  input  [8:0] cfg_intr_en_i,
  input  cfg_oneshot_done_i,

  input  adc_ctrl_reg2hw_intr_state_reg_t intr_state_i,
  input  adc_ctrl_reg2hw_intr_enable_reg_t intr_enable_i,
  input  adc_ctrl_reg2hw_intr_test_reg_t intr_test_i,

  output adc_ctrl_hw2reg_intr_state_reg_t intr_state_o,
  output adc_ctrl_hw2reg_adc_intr_status_reg_t adc_intr_status_o,

  output intr_debug_cable_o
);

  // synchronize status into appropriate interrupts
  logic [NumAdcFilter-1:0] filter_match_event;
  for (genvar i = 0; i < NumAdcFilter; i++) begin : gen_filter_status_sync
    prim_pulse_sync u_sync (
      .clk_src_i(clk_aon_i),
      .rst_src_ni(rst_aon_ni),
      .src_pulse_i(aon_filter_match_i[i]),
      .clk_dst_i(clk_i),
      .rst_dst_ni(rst_ni),
      .dst_pulse_o(filter_match_event[i])
    );
  end

  //To write into interrupt status register
  logic [1+NumAdcFilter-1:0] intr_events;
  assign intr_events = {cfg_oneshot_done_i, filter_match_event} & cfg_intr_en_i;

  assign adc_intr_status_o.cc_sink_det.de = intr_events[0];
  assign adc_intr_status_o.cc_1a5_sink_det.de = intr_events[1];
  assign adc_intr_status_o.cc_3a0_sink_det.de = intr_events[2];
  assign adc_intr_status_o.cc_src_det.de = intr_events[3];
  assign adc_intr_status_o.cc_1a5_src_det.de = intr_events[4];
  assign adc_intr_status_o.cc_src_det_flip.de = intr_events[5];
  assign adc_intr_status_o.cc_1a5_src_det_flip.de = intr_events[6];
  assign adc_intr_status_o.cc_discon.de = intr_events[7];
  assign adc_intr_status_o.oneshot.de = intr_events[8];

  assign adc_intr_status_o.cc_sink_det.d = 1'b1;
  assign adc_intr_status_o.cc_1a5_sink_det.d = 1'b1;
  assign adc_intr_status_o.cc_3a0_sink_det.d = 1'b1;
  assign adc_intr_status_o.cc_src_det.d = 1'b1;
  assign adc_intr_status_o.cc_1a5_src_det.d = 1'b1;
  assign adc_intr_status_o.cc_src_det_flip.d = 1'b1;
  assign adc_intr_status_o.cc_1a5_src_det_flip.d = 1'b1;
  assign adc_intr_status_o.cc_discon.d = 1'b1;
  assign adc_intr_status_o.oneshot.d = 1'b1;

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(1)) i_adc_ctrl_intr_o (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .event_intr_i           (|intr_events),
    .reg2hw_intr_enable_q_i (intr_enable_i.q),
    .reg2hw_intr_test_q_i   (intr_test_i.q),
    .reg2hw_intr_test_qe_i  (intr_test_i.qe),
    .reg2hw_intr_state_q_i  (intr_state_i.q),
    .hw2reg_intr_state_de_o (intr_state_o.de),
    .hw2reg_intr_state_d_o  (intr_state_o.d),
    .intr_o                 (intr_debug_cable_o)
  );

endmodule
