// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for alert_handler_esc_timer.
// Intended to be used with a formal tool.

module alert_handler_esc_timer_tb import alert_pkg::*; (
  input  clk_i,
  input  rst_ni,
  input  en_i,
  input  clr_i,
  input  accu_trig_i,
  input  accu_fail_i,
  input  timeout_en_i,
  input [EscCntDw-1:0] timeout_cyc_i,
  input [N_ESC_SEV-1:0] esc_en_i,
  input [N_ESC_SEV-1:0][PHASE_DW-1:0] esc_map_i,
  input [N_PHASES-1:0][EscCntDw-1:0] phase_cyc_i,
  input [PHASE_DW-1:0] crashdump_phase_i,
  output logic latch_crashdump_o,
  output logic esc_trig_o,
  output logic[EscCntDw-1:0] esc_cnt_o,
  output logic[N_ESC_SEV-1:0] esc_sig_req_o,
  output cstate_e esc_state_o
);

  alert_handler_esc_timer i_alert_handler_esc_timer (
    .clk_i,
    .rst_ni,
    .en_i,
    .clr_i,
    .accu_trig_i,
    .accu_fail_i,
    .timeout_en_i,
    .timeout_cyc_i,
    .esc_en_i,
    .esc_map_i,
    .phase_cyc_i,
    .crashdump_phase_i,
    .latch_crashdump_o,
    .esc_trig_o,
    .esc_cnt_o,
    .esc_sig_req_o,
    .esc_state_o
  );


endmodule : alert_handler_esc_timer_tb
