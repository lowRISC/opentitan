// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: RBOX interrupt Module
//
module rbox_intr import rbox_reg_pkg::*; (
  input  clk_i,
  input  rst_ni,
  input  rbox_combo_intr,
  input  rbox_key_intr,
  input  rbox_reg2hw_intr_state_reg_t intr_state_i,
  input  rbox_reg2hw_intr_enable_reg_t intr_enable_i,
  input  rbox_reg2hw_intr_test_reg_t intr_test_i,
  output rbox_hw2reg_intr_state_reg_t intr_state_o,
  output rbox_intr_o
);

  logic rbox_event;

  assign rbox_event = rbox_combo_intr | rbox_key_intr;

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(1)) i_rbox_intr_o (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .event_intr_i           (rbox_event),
    .reg2hw_intr_enable_q_i (intr_enable_i.q),
    .reg2hw_intr_test_q_i   (intr_test_i.q),
    .reg2hw_intr_test_qe_i  (intr_test_i.qe),
    .reg2hw_intr_state_q_i  (intr_state_i.q),
    .hw2reg_intr_state_de_o (intr_state_o.de),
    .hw2reg_intr_state_d_o  (intr_state_o.d),
    .intr_o                 (rbox_intr_o)
  );

endmodule
