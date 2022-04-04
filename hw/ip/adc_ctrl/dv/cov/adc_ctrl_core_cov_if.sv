// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for ADC_CTRL FSM

interface adc_ctrl_fsm_cov_if
  import adc_ctrl_pkg::*;
  (
  input logic clk_aon_i,
  input logic rst_aon_ni,
  input logic cfg_fsm_rst_i,
  input logic [15:0] np_sample_cnt_q,
  input logic [7:0] lp_sample_cnt_q,
  input fsm_state_e fsm_state_q
);
  `include "dv_fcov_macros.svh"
  localparam int NpSampleCntWidth = $bits(np_sample_cnt_q);
  localparam int MaxNpSampleCnt = 2 ** NpSampleCntWidth - 1;
  localparam int LpSampleCntWidth = $bits(lp_sample_cnt_q);
  localparam int MaxLpSampleCnt = 2 ** LpSampleCntWidth - 1;

  // Fsm state and counters when hardware reset is asserted
  covergroup adc_ctrl_hw_reset_cg @(negedge rst_aon_ni);
    option.per_instance = 1;
    np_sample_cnt_min_max_cp: coverpoint np_sample_cnt_q {
      bins min = {0}; bins max = {MaxNpSampleCnt};
    }
    np_sample_cnt_pow_cp: coverpoint $clog2(
        np_sample_cnt_q
    ) iff (np_sample_cnt_q inside {[0 : MaxNpSampleCnt - 1]}) {
      bins pow[NpSampleCntWidth] = {[0 : NpSampleCntWidth - 1]};
    }

    lp_sample_cnt_min_max_cp: coverpoint lp_sample_cnt_q {
      bins min = {0}; bins max = {MaxLpSampleCnt};
    }
    lp_sample_cnt_pow_cp: coverpoint $clog2(
        lp_sample_cnt_q
    ) iff (lp_sample_cnt_q inside {[0 : MaxLpSampleCnt - 1]}) {
      bins pow[LpSampleCntWidth] = {[0 : LpSampleCntWidth - 1]};
    }

    fsm_state_cp: coverpoint fsm_state_q;
  endgroup

  // Fsm state and counters when FSM reset is asserted
  covergroup adc_ctrl_fsm_reset_cg @(posedge clk_aon_i);
    option.per_instance = 1;
    np_sample_cnt_min_max_cp: coverpoint np_sample_cnt_q iff (cfg_fsm_rst_i == 1) {
      bins min = {0}; bins max = {MaxNpSampleCnt};
    }
    np_sample_cnt_pow_cp: coverpoint $clog2(
        np_sample_cnt_q
    ) iff ((cfg_fsm_rst_i == 1) && (np_sample_cnt_q inside {[0 : MaxNpSampleCnt - 1]})) {
      bins pow[NpSampleCntWidth] = {[0 : NpSampleCntWidth - 1]};
    }

    lp_sample_cnt_min_max_cp: coverpoint lp_sample_cnt_q iff (cfg_fsm_rst_i == 1) {
      bins min = {0}; bins max = {MaxLpSampleCnt};
    }
    lp_sample_cnt_pow_cp: coverpoint $clog2(
        lp_sample_cnt_q
    ) iff ((cfg_fsm_rst_i == 1) && (lp_sample_cnt_q inside {[0 : MaxLpSampleCnt - 1]})) {
      bins pow[LpSampleCntWidth] = {[0 : LpSampleCntWidth - 1]};
    }

    fsm_state_cp: coverpoint fsm_state_q iff (cfg_fsm_rst_i == 1);
  endgroup

  `DV_FCOV_INSTANTIATE_CG(adc_ctrl_hw_reset_cg)
  `DV_FCOV_INSTANTIATE_CG(adc_ctrl_fsm_reset_cg)
endinterface
