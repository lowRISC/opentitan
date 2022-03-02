// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module otbn_idle_checker
  import otbn_reg_pkg::*;
(
  input logic         clk_i,
  input logic         rst_ni,

  input otbn_reg2hw_t reg2hw,
  input otbn_hw2reg_t hw2reg,
  input logic         done_i,

  input prim_mubi_pkg::mubi4_t idle_o_i
);

  // Detect writes of CmdExecute to CMD. They only take effect if we are in state IDLE
  logic start_req, do_start;
  assign start_req = reg2hw.cmd.qe && (reg2hw.cmd.q == otbn_pkg::CmdExecute);
  assign do_start = start_req && (hw2reg.status.d == otbn_pkg::StatusIdle);

  // Our model of whether OTBN is running or not. We start on do_start and stop on done.
  logic running_q, running_d;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running_q <= 1'b0;
    end else begin
      running_q <= running_d;
    end
  end
  assign running_d = (do_start & ~running_q) | (running_q & ~done_i);

  // We should never see done_i when we're not already running. The converse assertion, that we
  // never see cmd_start when we are running, need not be true: the host can do that if it likes and
  // OTBN will ignore it. But we should never see do_start when we think we're running.
  `ASSERT(RunningIfDone_A, done_i |-> running_q)
  `ASSERT(IdleIfStart_A, do_start |-> !running_q)

  // Check that we've modelled the running/not-running logic correctly. The idle_o pin from OTBN
  // should be true iff running is false
  `ASSERT(IdleIfNotRunning_A, (idle_o_i == prim_mubi_pkg::MuBi4True) ^ running_q)

endmodule
