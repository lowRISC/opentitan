// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim_clk_timeout is a simple module that assesses whether the input clock
// has stopped ticking as measured by the reference clock.
//
// If both clocks are stopped for whatever reason, this module is effectively dead.

`include "prim_assert.sv"

module prim_clock_timeout #(
  parameter int TimeOutCnt = 16,
  localparam int CntWidth = prim_util_pkg::vbits(TimeOutCnt+1)
) (
  // clock to be checked
  input clk_chk_i,
  input rst_chk_ni,

  // clock used to measure whether clk_chk has stopped ticking
  input clk_i,
  input rst_ni,
  input en_i,
  output logic timeout_o
);

  logic [CntWidth-1:0] cnt;
  logic ack;
  logic timeout;
  assign timeout = int'(cnt) >= TimeOutCnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (ack || !en_i) begin
      cnt <= '0;
    end else if (timeout) begin
      cnt <= '{default: '1};
    end else if (en_i) begin
      cnt <= cnt + 1'b1;
    end
  end

  logic chk_req;
  prim_sync_reqack u_ref_timeout (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i(clk_chk_i),
    .rst_dst_ni(rst_chk_ni),
    .req_chk_i('0),
    .src_req_i(1'b1),
    .src_ack_o(ack),
    .dst_req_o(chk_req),
    .dst_ack_i(chk_req)
  );

  prim_flop #(
    .ResetValue('0)
  ) u_out (
    .clk_i,
    .rst_ni,
    .d_i(timeout),
    .q_o(timeout_o)
  );

endmodule // prim_clk_timeout
