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
  // interaction with ast
  output mubi4_t          all_clk_byp_req_o,
  input  mubi4_t          all_clk_byp_ack_i,
  output mubi4_t          io_clk_byp_req_o,
  input  mubi4_t          io_clk_byp_ack_i,
  // interaction with dividers
  input  [NumDivClks-1:0] step_down_acks_i,
  output mubi4_t          step_down_req_o
);

  import prim_mubi_pkg::MuBi4Width;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi4_and_hi;
  import prim_mubi_pkg::mubi4_or_hi;
  import prim_mubi_pkg::mubi4_test_false_strict;
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
    .lc_en_o(en)
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
  prim_lc_sender u_send (
   .clk_i,
   .rst_ni,
   .lc_en_i(&step_down_acks_sync ? lc_clk_byp_req[LcClkBypReqLcAck] : lc_ctrl_pkg::Off),
   .lc_en_o(lc_clk_byp_ack_o)
  );

  // software switch request handling
  mubi4_t dft_en;
  assign dft_en = (en == lc_ctrl_pkg::On) ? MuBi4True : MuBi4False;

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

  // divider step down handling
  mubi4_t io_clk_byp_ack;
  mubi4_t all_clk_byp_ack;

  prim_mubi4_sync #(
    .AsyncOn(1),
    .ResetValue(MuBi4False)
  ) u_io_ack_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(io_clk_byp_ack_i),
    .mubi_o({io_clk_byp_ack})
  );

  prim_mubi4_sync #(
    .AsyncOn(1),
    .ResetValue(MuBi4False)
  ) u_all_ack_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(all_clk_byp_ack_i),
    .mubi_o({all_clk_byp_ack})
  );

  // create individual requests
  mubi4_t lc_step_down_req;
  assign lc_step_down_req = mubi4_and_hi(io_clk_byp_req_o, io_clk_byp_ack);

  // When requesting a switch, the low speed indication is used to determine step down.
  // Once switched, the low speed indication is not looked at again until software request
  // is de-asserted.
  mubi4_t sw_step_down_en;
  mubi4_t sw_step_down_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sw_step_down_en <= MuBi4False;
    end else if (mubi4_test_true_strict(all_clk_byp_req_o) &&
                 mubi4_test_true_strict(all_clk_byp_ack)) begin
      sw_step_down_en <= MuBi4True;
    end else if (
      mubi4_test_true_strict(sw_step_down_en) &&
      mubi4_test_false_strict(all_clk_byp_req_o) &&
      mubi4_test_false_strict(all_clk_byp_ack)) begin
      sw_step_down_en <= MuBi4False;
    end
  end
  // when in external clock state, allow low speed select to directly control
  // clock divider.

  // TODO
  // This will be updated to a different signaling, see #10890
  assign sw_step_down_req = sw_step_down_en;

  // combine requests
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      step_down_req_o <= MuBi4False;
    end else begin
      step_down_req_o <= mubi4_or_hi(lc_step_down_req, sw_step_down_req);
    end
  end


endmodule // clkmgr_byp
