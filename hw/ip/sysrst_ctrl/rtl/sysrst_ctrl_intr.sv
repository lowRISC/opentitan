// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl interrupt Module
//
module sysrst_ctrl_intr
  import sysrst_ctrl_reg_pkg::*;
(
  input  clk_aon_i,
  input  rst_aon_ni,
  input  clk_i,
  input  rst_ni,

  input  [NumKeyIntr-1:0] aon_l2h_key_intr_i,
  input  [NumKeyIntr-1:0] aon_h2l_key_intr_i,
  input  [NumCombo-1:0]   aon_combo_intr_i,
  input                   aon_ulp_wakeup_pulse_i,

  input  sysrst_ctrl_reg2hw_wkup_status_reg_t       wkup_status_i,
  input  sysrst_ctrl_reg2hw_intr_state_reg_t        intr_state_i,
  input  sysrst_ctrl_reg2hw_intr_enable_reg_t       intr_enable_i,
  input  sysrst_ctrl_reg2hw_intr_test_reg_t         intr_test_i,
  input  sysrst_ctrl_reg2hw_key_intr_status_reg_t   key_intr_status_i,
  input  sysrst_ctrl_reg2hw_combo_intr_status_reg_t combo_intr_status_i,
  input  sysrst_ctrl_reg2hw_ulp_status_reg_t        ulp_status_i,

  output sysrst_ctrl_hw2reg_wkup_status_reg_t       wkup_status_o,
  output sysrst_ctrl_hw2reg_intr_state_reg_t        intr_state_o,
  output sysrst_ctrl_hw2reg_key_intr_status_reg_t   key_intr_status_o,
  output sysrst_ctrl_hw2reg_combo_intr_status_reg_t combo_intr_status_o,
  output sysrst_ctrl_hw2reg_ulp_status_reg_t        ulp_status_o,

  output intr_o,
  output aon_wkup_req_o
);

  // Aggregate number of events to sync over.
  localparam int NumAonIntrEvents = 2*NumKeyIntr + NumCombo + 1;
  logic [NumAonIntrEvents-1:0] aon_reqs;
  assign aon_reqs = {aon_ulp_wakeup_pulse_i,
                     aon_combo_intr_i,
                     aon_h2l_key_intr_i,
                     aon_l2h_key_intr_i};

  // Latch any event in the AON domain for generating the wakeup request.
  assign wkup_status_o.de = |aon_reqs;
  assign wkup_status_o.d = 1'b1;
  assign aon_wkup_req_o = wkup_status_i.q;

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

  // staging has pending requests
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

  // To write into interrupt status registers.
  logic [NumKeyIntr-1:0] l2h_key_intr, h2l_key_intr;
  logic [NumCombo-1:0] combo_intr;
  logic ulp_wakeup_pulse;

  assign {ulp_wakeup_pulse,
          combo_intr,
          h2l_key_intr,
          l2h_key_intr} = {NumAonIntrEvents{dst_ack_q}} & req_hold_q;

  // Key IRQ status
  assign {key_intr_status_o.pwrb_l2h.de,
          key_intr_status_o.key0_in_l2h.de,
          key_intr_status_o.key1_in_l2h.de,
          key_intr_status_o.key2_in_l2h.de,
          key_intr_status_o.ac_present_l2h.de,
          key_intr_status_o.ec_rst_l_l2h.de,
          key_intr_status_o.flash_wp_l_l2h.de} = l2h_key_intr;

  assign {key_intr_status_o.pwrb_h2l.de,
          key_intr_status_o.key0_in_h2l.de,
          key_intr_status_o.key1_in_h2l.de,
          key_intr_status_o.key2_in_h2l.de,
          key_intr_status_o.ac_present_h2l.de,
          key_intr_status_o.ec_rst_l_h2l.de,
          key_intr_status_o.flash_wp_l_h2l.de} = h2l_key_intr;

  assign key_intr_status_o.pwrb_h2l.d = 1'b1;
  assign key_intr_status_o.pwrb_l2h.d = 1'b1;
  assign key_intr_status_o.key0_in_h2l.d = 1'b1;
  assign key_intr_status_o.key0_in_l2h.d = 1'b1;
  assign key_intr_status_o.key1_in_h2l.d = 1'b1;
  assign key_intr_status_o.key1_in_l2h.d = 1'b1;
  assign key_intr_status_o.key2_in_h2l.d = 1'b1;
  assign key_intr_status_o.key2_in_l2h.d = 1'b1;
  assign key_intr_status_o.ac_present_h2l.d = 1'b1;
  assign key_intr_status_o.ac_present_l2h.d = 1'b1;
  assign key_intr_status_o.ec_rst_l_h2l.d = 1'b1;
  assign key_intr_status_o.ec_rst_l_l2h.d = 1'b1;
  assign key_intr_status_o.flash_wp_l_h2l.d = 1'b1;
  assign key_intr_status_o.flash_wp_l_l2h.d = 1'b1;

  // Combo IRQ status
  assign combo_intr_status_o.combo0_h2l.d = 1'b1;
  assign combo_intr_status_o.combo1_h2l.d = 1'b1;
  assign combo_intr_status_o.combo2_h2l.d = 1'b1;
  assign combo_intr_status_o.combo3_h2l.d = 1'b1;
  assign {combo_intr_status_o.combo3_h2l.de,
          combo_intr_status_o.combo2_h2l.de,
          combo_intr_status_o.combo1_h2l.de,
          combo_intr_status_o.combo0_h2l.de} = combo_intr;

  // ULP wakeup status
  assign ulp_status_o.d = 1'b1;
  assign ulp_status_o.de = ulp_wakeup_pulse;

  // Aggregate interrupt event statuses.
  logic intr_event_status;
  assign intr_event_status = |{ulp_status_i,
                               combo_intr_status_i,
                               key_intr_status_i};

  // instantiate interrupt hardware primitive
  prim_intr_hw #(
   .Width(1),
   .IntrT("Status")
  ) u_sysrst_ctrl_intr_o (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event_status),
    .reg2hw_intr_enable_q_i (intr_enable_i.q),
    .reg2hw_intr_test_q_i   (intr_test_i.q),
    .reg2hw_intr_test_qe_i  (intr_test_i.qe),
    .reg2hw_intr_state_q_i  (intr_state_i.q),
    .hw2reg_intr_state_de_o (intr_state_o.de),
    .hw2reg_intr_state_d_o  (intr_state_o.d),
    .intr_o
  );

endmodule
