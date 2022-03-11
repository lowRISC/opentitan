// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// System verilog assertions for the adc_ctrl_fsm module
module adc_ctrl_fsm_sva (
  // adc_ctrl_fsm ports
  input logic clk_aon_i,
  input logic rst_aon_ni,
  input logic cfg_fsm_rst_i,
  // adc_ctrl_fsm signals
  input logic [4:0] fsm_state_q,
  input logic [3:0] pwrup_timer_cnt_q,
  input logic [23:0] wakeup_timer_cnt_q,
  input logic [15:0] np_sample_cnt_q,
  input logic [7:0] lp_sample_cnt_q
);

  localparam logic [4:0] FsmResetState = 0;

  // FSM software reset
  `ASSERT(FsmStateSwReset_A, cfg_fsm_rst_i |=> fsm_state_q == FsmResetState, clk_aon_i, !rst_aon_ni)
  `ASSERT(PwrupTimerCntSwReset_A, cfg_fsm_rst_i |=> pwrup_timer_cnt_q == 0, clk_aon_i, !rst_aon_ni)
  `ASSERT(WakeupTimerCntSwReset_A, cfg_fsm_rst_i |=> wakeup_timer_cnt_q == 0, clk_aon_i,
          !rst_aon_ni)
  `ASSERT(NpSampleCntSwReset_A, cfg_fsm_rst_i |=> np_sample_cnt_q == 0, clk_aon_i, !rst_aon_ni)
  `ASSERT(LpSampleCntSwReset_A, cfg_fsm_rst_i |=> lp_sample_cnt_q == 0, clk_aon_i, !rst_aon_ni)


  // FSM hardware reset - checks first clk_aon_i after every hardware reset
  `ASSERT(FsmStateHwReset_A, 1 |=> (@(posedge clk_aon_i) fsm_state_q == FsmResetState), !rst_aon_ni,
          0)
  `ASSERT(PwrupTimerCntHwReset_A, 1 |=> (@(posedge clk_aon_i) pwrup_timer_cnt_q == 0), !rst_aon_ni,
          0)
  `ASSERT(WakeupTimerCntHwReset_A, 1 |=> (@(posedge clk_aon_i) wakeup_timer_cnt_q == 0),
          !rst_aon_ni, 0)
  `ASSERT(NpSampleCntHwReset_A, 1 |=> (@(posedge clk_aon_i) np_sample_cnt_q == 0), !rst_aon_ni, 0)
  `ASSERT(LpSampleCntHwReset_A, 1 |=> (@(posedge clk_aon_i) lp_sample_cnt_q == 0), !rst_aon_ni, 0)

endmodule
