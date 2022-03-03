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

  input prim_mubi_pkg::mubi4_t idle_o_i,

  input logic otbn_dmem_scramble_key_req_busy_i,
  input logic otbn_imem_scramble_key_req_busy_i,

  input logic [7:0] status_q_i
);

  // Detect writes to CMD. They only take effect if we are in state IDLE
  logic cmd_operation, start_req, do_start;

  assign cmd_operation = reg2hw.cmd.q inside {otbn_pkg::CmdSecWipeImem,
                                              otbn_pkg::CmdSecWipeDmem,
                                              otbn_pkg::CmdExecute};

  assign start_req = reg2hw.cmd.qe && cmd_operation;

  assign do_start = start_req && (hw2reg.status.d == otbn_pkg::StatusIdle);

  // Our model of whether OTBN is running or not. We start on do_start and stop on done.
  logic running_qq, running_q, running_d;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running_q  <= 1'b0;
      running_qq <= 1'b0;
    end else begin
      running_q  <= running_d;
      running_qq <= running_q;
    end
  end
  assign running_d = (do_start & ~running_q) | (running_q & ~done_i);

  // We should never see done_i when we're not already running. The converse assertion, that we
  // never see cmd_start when we are running, need not be true: the host can do that if it likes and
  // OTBN will ignore it. But we should never see do_start when we think we're running.
  `ASSERT(RunningIfDone_A, done_i |-> running_q)
  `ASSERT(IdleIfStart_A, do_start |-> !running_q)

  // Key rotation (used in the logic below) can delay the idle signal. This signal is flopped an
  // extra time to stay "busy" for an extra cycle, so we mirror that here.
  logic rotating_keys, rotating_keys_q, keys_busy;
  assign rotating_keys = otbn_dmem_scramble_key_req_busy_i | otbn_imem_scramble_key_req_busy_i;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rotating_keys_q <= 0;
    end else begin
      rotating_keys_q <= rotating_keys;
    end
  end
  assign keys_busy = rotating_keys | rotating_keys_q;

  // Check that we've modelled the running/not-running logic correctly. Most of the time, the idle_o
  // pin should be false when we're running an operation of some sort and true otherwise. The only
  // slight complication comes comes about with fatal errors, where we go into LOCKED state (and
  // aren't "running an operation"), but still do a pair of OTP key requests to wipe IMEM and DMEM
  // in the background.
  //
  // So our assertions should be:
  //
  //  - If tracking the start/done registers suggests we should be running, idle should be false
  //    (NotIdleIfRunning_A)
  //
  //  - If it suggests we should not be running and the STATUS register has a value other than
  //    LOCKED, idle should be true. (IdleIfNotRunningOrLocked_A)
  //
  //  - If the STATUS register has value LOCKED then idle should be true iff neither of the key
  //    requests are busy. (NotIdleIfLockedAndRotatingKeys_A; IdleIfLockedAndNotRotatingKeys_A)
  //
  //  - We should never start a new key request once STATUS has value LOCKED
  //    (NoStartKeyRotationWhenLocked_A)
  //
  //  - We should only have a key request in flight if we are either running (as tracked by
  //    start/done) or LOCKED (OnlyKeyRotationWhenRunningOrLocked_A)
  //
  //  - We should never think we're running when STATUS has value LOCKED (NotRunningWhenLocked_A)

  `ASSERT(NotIdleIfRunning_A,
          running_q |-> ##[0:1] (idle_o_i == prim_mubi_pkg::MuBi4False))

  `ASSERT(IdleIfNotRunningOrLocked_A,
          !(running_qq || status_q_i == otbn_pkg::StatusLocked) |->
          (idle_o_i == prim_mubi_pkg::MuBi4True))

  `ASSERT(NotIdleIfLockedAndRotatingKeys_A,
          ((status_q_i == otbn_pkg::StatusLocked) && keys_busy) |->
          (idle_o_i == prim_mubi_pkg::MuBi4False))
  `ASSERT(IdleIfLockedAndNotRotatingKeys_A,
          ((status_q_i == otbn_pkg::StatusLocked) && !keys_busy) |->
          (idle_o_i == prim_mubi_pkg::MuBi4True))

  `ASSERT(NoStartKeyRotationWhenLocked_A,
          (status_q_i == otbn_pkg::StatusLocked) |-> !$rose(keys_busy))

  `ASSERT(OnlyKeyRotationWhenRunningOrLocked_A,
          keys_busy |-> (running_q || (status_q_i == otbn_pkg::StatusLocked)))

  `ASSERT(NotRunningWhenLocked_A,
          !((status_q_i == otbn_pkg::StatusLocked) && running_q))

endmodule
