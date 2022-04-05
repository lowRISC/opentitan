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


  // aon_filter_match is split into staging and request portions.
  // The staging portion always absorbs the incoming event pulse.
  // The request portion on the other hand does not change until
  // a request/ack handshake cycle has completed.

  logic [NumAdcFilter-1:0] staging_filter_match;
  logic aon_ld_req;

  // staging portion takes on the value of the incoming event match
  // and clears when it is snapshot into request hold.
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
     if (!rst_aon_ni) begin
        staging_filter_match <= '0;
     end else if (aon_ld_req && |aon_filter_match_i) begin
        staging_filter_match <= aon_filter_match_i;
     end else if (aon_ld_req) begin
        staging_filter_match <= '0;
     end else if (|aon_filter_match_i) begin
        staging_filter_match <= staging_filter_match | aon_filter_match_i;
     end
  end

  logic [NumAdcFilter-1:0] aon_req_hold;
  logic aon_ack;

  // staging has pending requsts
  assign aon_ld_req = (aon_req_hold == '0) & |staging_filter_match;

  // request hold self clears when the handshake cycle is complete
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
       aon_req_hold <= '0;
    end else if (aon_ld_req) begin
       aon_req_hold <= staging_filter_match;
    end else if (aon_ack) begin
       aon_req_hold <= '0;
    end
  end

  logic filter_match_event;
  prim_sync_reqack u_match_sync (
    .clk_src_i(clk_aon_i),
    .rst_src_ni(rst_aon_ni),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .req_chk_i(1'b1),
    .src_req_i(|aon_req_hold),
    .src_ack_o(aon_ack),
    .dst_req_o(filter_match_event),
    .dst_ack_i(filter_match_event)
  );

  //To write into interrupt status register
  logic [1+NumAdcFilter-1:0] intr_events;
  assign intr_events = {cfg_oneshot_done_i,
                        {NumAdcFilter{filter_match_event}} & aon_req_hold} & cfg_intr_en_i;

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
