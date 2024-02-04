// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Clock manager measurement and timeout checks

module clkmgr_meas_chk
  import prim_mubi_pkg::mubi4_t;
#(
  // Maximum value of input clock counts over measurement period
  parameter int Cnt = 16,
  // Maximum value of reference clock counts over measurement period
  parameter int RefCnt = 1,
  localparam int CntWidth = prim_util_pkg::vbits(Cnt)
) (
  // the local operating clock
  input clk_i,
  input rst_ni,
  // the clock we are measuring
  input clk_src_i,
  input rst_src_ni,
  // the reference clock we are measuring against
  input clk_ref_i,
  input rst_ref_ni,
  // controls all provided on src clock
  input src_en_i,
  input [CntWidth-1:0] src_max_cnt_i,
  input [CntWidth-1:0] src_min_cnt_i,
  input mubi4_t src_cfg_meas_en_i,
  output logic src_cfg_meas_en_valid_o,
  output mubi4_t src_cfg_meas_en_o,
  // calibration ready input provided on local operating clock
  input mubi4_t calib_rdy_i,
  // error output are provided on local operating clock
  output logic meas_err_o,
  output logic timeout_err_o
);

  logic src_fast_err;
  logic src_slow_err;
  logic ref_timeout_err;

  prim_clock_meas #(
    .Cnt(Cnt),
    .RefCnt(RefCnt),
    .ClkTimeOutChkEn(1'b1),
    .RefTimeOutChkEn(1'b0)
  ) u_meas (
    .clk_i(clk_src_i),
    .rst_ni(rst_src_ni),
    .clk_ref_i,
    .rst_ref_ni,
    .en_i(src_en_i),
    .max_cnt(src_max_cnt_i),
    .min_cnt(src_min_cnt_i),
    .valid_o(),
    .fast_o(src_fast_err),
    .slow_o(src_slow_err),
    .timeout_clk_ref_o(),
    .ref_timeout_clk_o(ref_timeout_err)
  );

  mubi4_t src_calib_rdy;
  prim_mubi4_sync #(
    .AsyncOn(1),
    .ResetValue(prim_mubi_pkg::MuBi4False)
  ) u_calib_rdy_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(calib_rdy_i),
    .mubi_o({src_calib_rdy})
  );

  // if clocks become uncalibrated, switch off measurement controls
  always_comb begin
    src_cfg_meas_en_valid_o = '0;
    src_cfg_meas_en_o = src_cfg_meas_en_i;

    // if calibration is lost when measurement is currently enabled,
    // disable measurement enable.
    if (prim_mubi_pkg::mubi4_test_false_strict(src_calib_rdy) &&
        prim_mubi_pkg::mubi4_test_true_loose(src_cfg_meas_en_o)) begin
      src_cfg_meas_en_valid_o = 1'b1;
      src_cfg_meas_en_o = prim_mubi_pkg::MuBi4False;
    end
  end

  // A reqack module is used here instead of a pulse_saync
  // because the source pulses may toggle too fast for the
  // the destination to receive.
  logic src_err_req, src_err_ack;
  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_err_req <= '0;
    end else if (src_fast_err || src_slow_err) begin
      src_err_req <= 1'b1;
    end else if (src_err_req && src_err_ack) begin
      src_err_req <= '0;
    end
  end

  prim_sync_reqack u_err_sync (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .req_chk_i(1'b1),
    .src_req_i(src_err_req),
    .src_ack_o(src_err_ack),
    .dst_req_o(meas_err_o),
    .dst_ack_i(meas_err_o)
  );

  prim_edge_detector #(
    .Width(1),
    .ResetValue('0),
    .EnSync(1'b1)
  ) u_timeout_err_sync (
    .clk_i,
    .rst_ni,
    .d_i(ref_timeout_err),
    .q_sync_o(),
    .q_posedge_pulse_o(timeout_err_o),
    .q_negedge_pulse_o()
  );

endmodule // clkmgr_meas_chk
