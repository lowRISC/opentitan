// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// System verilog assertions for the adc_ctrl_fsm module

// An interface that is bound into adc_ctrl_fsm, capturing ports with .* (so the input ports are
// named to match signals inside that module).

interface adc_ctrl_fsm_sva_if
  import adc_ctrl_pkg::*;
(
  // adc_ctrl_fsm ports
  input logic clk_aon_i,
  input logic rst_aon_ni,
  input logic cfg_fsm_rst_i,

  // adc_ctrl_fsm signals
  input fsm_state_e  fsm_state_q,
  input logic [3:0]  pwrup_timer_cnt_q,
  input logic [23:0] wakeup_timer_cnt_q,
  input logic [15:0] np_sample_cnt_q,
  input logic [7:0]  lp_sample_cnt_q
);

  localparam fsm_state_e FsmResetState = PWRDN;

  default clocking @(posedge clk_aon_i); endclocking

  if (1) begin : gen_aon_assertions
    default disable iff !rst_aon_ni;

    // FSM software reset
    FsmStateSwReset_A: assert property (cfg_fsm_rst_i |=> fsm_state_q == FsmResetState);
    PwrupTimerCntSwReset_A: assert property (cfg_fsm_rst_i |=> pwrup_timer_cnt_q == 0);
    WakeupTimerCntSwReset_A: assert property (cfg_fsm_rst_i |=> wakeup_timer_cnt_q == 0);
    NpSampleCntSwReset_A: assert property (cfg_fsm_rst_i |=> np_sample_cnt_q == 0);
    LpSampleCntSwReset_A: assert property (cfg_fsm_rst_i |=> lp_sample_cnt_q == 0);

    // Check connectivity of the state output register (this is used for debug only).
    FsmDebugOut_A: assert property (fsm_state_q === tb.dut.u_reg.hw2reg.adc_fsm_state.d);
  end

  // FSM hardware reset
  //
  // These assertions contain properties that have a check on the first posedge of clk_aon_i after
  // the hardware reset is applied. Note that this clock edge may happen during or after the reset
  // (and the assertions are expected to be true either way).

  bit start_of_reset;
  always @(negedge rst_aon_ni) begin
    start_of_reset <= 1;
  end
  always @(posedge clk_aon_i) begin
    start_of_reset <= 0;
  end

  FsmStateHwReset_A: assert property (start_of_reset -> fsm_state_q == FsmResetState);
  PwrupTimerCntHwReset_A: assert property (start_of_reset -> pwrup_timer_cnt_q == 0);
  WakeupTimerCntHwReset_A: assert property (start_of_reset -> wakeup_timer_cnt_q == 0);
  NpSampleCntHwReset_A: assert property (start_of_reset -> np_sample_cnt_q == 0);
  LpSampleCntHwReset_A: assert property (start_of_reset -> lp_sample_cnt_q == 0);

endinterface
