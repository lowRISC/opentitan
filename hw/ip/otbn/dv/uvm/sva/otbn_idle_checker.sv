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
  input logic         done_i,

  input logic         idle_o_i
);

  // Detect writes of CmdExecute to CMD
  logic cmd_start;
  assign cmd_start = reg2hw.cmd.qe && (reg2hw.cmd.q == otbn_pkg::CmdExecute);

  // Our model of whether OTBN is running or not. We start on cmd_start if we're not already running
  // and stop on done if we are. Note that the "running" signal includes the cycle that we see
  // cmd_start
  logic running_q, running_d;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running_q <= 1'b0;
    end else begin
      running_q <= running_d;
    end
  end
  assign running_d = (cmd_start & ~running_q) | (running_q & ~done_i);

  // We should never see done_i when we're not already running. (The converse assertion, that we
  // never see cmd_start when we are running, need not be true: the host can do that if it likes and
  // OTBN will ignore it).
  `ASSERT(RunningIfDone_A, done_i |-> running_q)

  // Check that we've modelled the running/not-running logic correctly. The idle_o pin from OTBN
  // should be true iff running is false
  `ASSERT(IdleIfNotRunning_A, idle_o_i ^ running_q)

endmodule
