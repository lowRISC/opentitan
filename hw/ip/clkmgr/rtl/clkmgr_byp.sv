// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Handle clock manager bypass requests

module clkmgr_byp
  import clkmgr_pkg::*;
  import lc_ctrl_pkg::lc_tx_t;
  import prim_mubi_pkg::mubi4_t;
# (
  parameter int NumDivClks = 1
) (
  input                   clk_i,
  input                   rst_ni,
  // interaction with lc_ctrl
  input  lc_tx_t          en_i,
  input  lc_tx_t          lc_clk_byp_req_i,
  output lc_tx_t          lc_clk_byp_ack_o,
  // interaction with software
  input  mubi4_t          byp_req_i,
  output mubi4_t          byp_ack_o,
  input  mubi4_t          hi_speed_sel_i,
  // interaction with ast
  output mubi4_t          all_clk_byp_req_o,
  input  mubi4_t          all_clk_byp_ack_i,
  output mubi4_t          io_clk_byp_req_o,
  input  mubi4_t          io_clk_byp_ack_i,
  output mubi4_t          hi_speed_sel_o,
  // interaction with dividers
  input  [NumDivClks-1:0] step_down_acks_i
);

  import prim_mubi_pkg::MuBi4Width;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi4_and_hi;
  import prim_mubi_pkg::mubi4_test_true_strict;

  // synchornize incoming lc signals
  lc_tx_t en;
  prim_lc_sync #(
    .NumCopies(1),
    .AsyncOn(1),
    .ResetValueIsOn(0)
  ) u_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(en_i),
    .lc_en_o({en})
  );

  typedef enum logic [1:0] {
    LcClkBypReqIoReq,
    LcClkBypReqLcAck,
    LcClkBypReqLast
  } lc_clk_byp_req_e;

  lc_tx_t [LcClkBypReqLast-1:0] lc_clk_byp_req;
  prim_lc_sync #(
    .NumCopies(int'(LcClkBypReqLast)),
    .AsyncOn(1),
    .ResetValueIsOn(0)
  ) u_lc_byp_req (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_clk_byp_req_i),
    .lc_en_o(lc_clk_byp_req)
  );

  // synchronize step down acks
  logic [NumDivClks-1:0] step_down_acks_sync;
  prim_flop #(
    .Width(NumDivClks),
    .ResetValue(0)
  ) u_step_down_acks_sync (
    .clk_i,
    .rst_ni,
    .d_i(step_down_acks_i),
    .q_o(step_down_acks_sync)
  );

  // life cycle handling
  mubi4_t io_clk_byp_req_d;
  assign io_clk_byp_req_d = (lc_clk_byp_req[LcClkBypReqIoReq] == lc_ctrl_pkg::On) ?
                            MuBi4True :
                            MuBi4False;

  prim_mubi4_sender #(
    .ResetValue(MuBi4False),
    .EnSecBuf(1)
  ) u_io_byp_req (
    .clk_i,
    .rst_ni,
    .mubi_i(io_clk_byp_req_d),
    .mubi_o(io_clk_byp_req_o)
  );

  // only ack the lc_ctrl if it made a request.
  mubi4_t io_clk_byp_ack;
  prim_lc_sender u_send (
   .clk_i,
   .rst_ni,
   .lc_en_i(&step_down_acks_sync & mubi4_test_true_strict(io_clk_byp_ack) ?
            lc_clk_byp_req[LcClkBypReqLcAck] : lc_ctrl_pkg::Off),
   .lc_en_o(lc_clk_byp_ack_o)
  );

  // software switch request handling
  mubi4_t dft_en;
  assign dft_en = lc_ctrl_pkg::lc_to_mubi4(en);

  mubi4_t all_clk_byp_req_d;
  assign all_clk_byp_req_d = mubi4_and_hi(byp_req_i, dft_en);

  prim_mubi4_sender #(
    .AsyncOn(1),
    .ResetValue(MuBi4False),
    .EnSecBuf(1)
  ) u_all_byp_req (
    .clk_i,
    .rst_ni,
    .mubi_i(all_clk_byp_req_d),
    .mubi_o(all_clk_byp_req_o)
  );

  prim_mubi4_sync #(
    .AsyncOn(1),
    .StabilityCheck(1),
    .ResetValue(MuBi4False)
  ) u_io_ack_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(io_clk_byp_ack_i),
    .mubi_o({io_clk_byp_ack})
  );

  // since div_step_down_req is now directly fed externally, there is no longer
  // a use for the related 'ack' signals
  prim_mubi4_sync #(
    .AsyncOn(1),
    .StabilityCheck(1),
    .ResetValue(MuBi4False)
  ) u_all_ack_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(all_clk_byp_ack_i),
    .mubi_o({byp_ack_o})
  );

  // the software high speed select is valid only when software requests clock
  // bypass
  prim_mubi4_sender #(
    .AsyncOn(1),
    .ResetValue(MuBi4True)
  ) u_hi_speed_sel (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi4_and_hi(all_clk_byp_req_d, hi_speed_sel_i)),
    .mubi_o(hi_speed_sel_o)
  );

endmodule // clkmgr_byp
