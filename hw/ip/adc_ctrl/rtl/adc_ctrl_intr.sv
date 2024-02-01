// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: adc_ctrl interrupt Module
//
module adc_ctrl_intr
  import adc_ctrl_reg_pkg::*;
#(
) (
  input  clk_aon_i,
  input  rst_aon_ni,
  input  clk_i,
  input  rst_ni,

  input  [NumAdcFilter-1:0] aon_filter_match_i,
  input  aon_fsm_trans_i,
  input  cfg_oneshot_done_i,

  input  [NumAdcFilter-1:0] cfg_intr_en_i,
  input  cfg_intr_trans_en_i,
  input  cfg_oneshot_done_en_i,

  input  adc_ctrl_reg2hw_intr_state_reg_t intr_state_i,
  input  adc_ctrl_reg2hw_intr_enable_reg_t intr_enable_i,
  input  adc_ctrl_reg2hw_intr_test_reg_t intr_test_i,

  output adc_ctrl_hw2reg_intr_state_reg_t intr_state_o,
  input  adc_ctrl_reg2hw_adc_intr_status_reg_t adc_intr_status_i,
  output adc_ctrl_hw2reg_adc_intr_status_reg_t adc_intr_status_o,

  output intr_o
);


  // Number of filters and FSM transition interrupt.
  localparam int NumAonIntrEvents = NumAdcFilter + 1;
  logic [NumAonIntrEvents-1:0] aon_reqs;
  assign aon_reqs = {aon_fsm_trans_i, aon_filter_match_i};

  // aon interrupt requests are split into staging and request portions.
  // The staging portion always absorbs the incoming event pulse.
  // The request portion on the other hand does not change until
  // a request/ack handshake cycle has completed.
  logic [NumAonIntrEvents-1:0] aon_staging_reqs_q;
  logic aon_ld_req;

  // staging portion takes on the value of the incoming event match
  // and clears when it is snapshot into request hold.
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
     if (!rst_aon_ni) begin
        aon_staging_reqs_q <= '0;
     end else if (aon_ld_req) begin
        aon_staging_reqs_q <= aon_reqs;
     end else if (|aon_reqs) begin
        aon_staging_reqs_q <= aon_staging_reqs_q | aon_reqs;
     end
  end

  logic [NumAonIntrEvents-1:0] aon_req_hold_q;
  logic aon_ack;

  // staging has pending requsts
  assign aon_ld_req = (aon_req_hold_q == '0) && |aon_staging_reqs_q;

  // request hold self clears when the handshake cycle is complete
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
     if (!rst_aon_ni) begin
        aon_req_hold_q <= '0;
     end else if (aon_ld_req) begin
        aon_req_hold_q <= aon_staging_reqs_q;
     end else if (aon_ack) begin
        aon_req_hold_q <= '0;
     end
  end

  logic dst_ack;
  prim_sync_reqack u_match_sync (
    .clk_src_i(clk_aon_i),
    .rst_src_ni(rst_aon_ni),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .req_chk_i(1'b1),
    .src_req_i(|aon_req_hold_q),
    .src_ack_o(aon_ack),
    .dst_req_o(dst_ack),
    .dst_ack_i(dst_ack)
  );

  // Holding reg after the CDC. Note that aon_req_hold_q does not change until the handshake has
  // been completed, hence we can sample it safely upon a dst_ack pulse.
  logic dst_ack_q;
  logic [NumAonIntrEvents-1:0] req_hold_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_hold_q <= '0;
      dst_ack_q <= 1'b0;
    end else begin
      dst_ack_q <= dst_ack;
      if (dst_ack) begin
        req_hold_q <= aon_req_hold_q;
      end
    end
  end

  assign adc_intr_status_o.trans.de = cfg_intr_trans_en_i && dst_ack_q && req_hold_q[8];
  assign adc_intr_status_o.trans.d = 1'b1;
  // Since interrupt events are pulsed, when successive events arrive we need to make sure to
  // hold the previously latched values
  logic [NumAdcFilter-1:0] match_events;
  assign match_events = cfg_intr_en_i & {NumAdcFilter{dst_ack_q}} & req_hold_q[NumAdcFilter-1:0];
  assign adc_intr_status_o.match.de = |match_events;
  assign adc_intr_status_o.match.d = match_events | adc_intr_status_i.match.q;
  // Note that we're also adding the non-AON interrupt source cfg_oneshot_done_i at this point.
  assign adc_intr_status_o.oneshot.de = cfg_oneshot_done_i && cfg_oneshot_done_en_i;
  assign adc_intr_status_o.oneshot.d = 1'b1;

  logic status_irq_value;
  assign status_irq_value = |{adc_intr_status_i.oneshot.q,
                              adc_intr_status_i.trans.q,
                              adc_intr_status_i.match.q};

  // instantiate interrupt hardware primitive
  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) i_adc_ctrl_intr_o (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .event_intr_i           (status_irq_value),
    .reg2hw_intr_enable_q_i (intr_enable_i.q),
    .reg2hw_intr_test_q_i   (intr_test_i.q),
    .reg2hw_intr_test_qe_i  (intr_test_i.qe),
    .reg2hw_intr_state_q_i  (intr_state_i.q),
    .hw2reg_intr_state_de_o (intr_state_o.de),
    .hw2reg_intr_state_d_o  (intr_state_o.d),
    .intr_o
  );

endmodule
