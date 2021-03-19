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

  input logic         idle_o_i
);

  // Detect writes of 1 to CMD.START (the "start" bit has been eaten by reggen because the register
  // only contains the one bit).
  logic cmd_start;
  assign cmd_start = reg2hw.cmd.qe & reg2hw.cmd.q;

  // Detect the DONE signal. Note that snooping on intr_state.d and intr_state.de like this will
  // pick it up irrespective of whether the interrupt is enabled and whether the previous state (in
  // the 'q' part) was cleared.
  logic done;
  assign done = hw2reg.intr_state.de & hw2reg.intr_state.d;

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
  assign running_d = (cmd_start & ~running_q) | (running_q & ~done);

  // We should never see done when we're not already running. (The converse assertion, that we never
  // see cmd_start when we are running, need not be true: the host can do that if it likes and OTBN
  // will ignore it).
  `ASSERT(RunningIfDone_A, done |-> running_q)

  // Check that we've modelled the running/not-running logic correctly. The idle_o pin from OTBN
  // should be true iff running is false
  `ASSERT(IdleIfNotRunning_A, idle_o_i ^ running_q)

endmodule
