// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module otbn_idle_checker
  import otbn_reg_pkg::*;
  import otbn_pkg::*;
(
  input logic         clk_i,
  input logic         rst_ni,

  input otbn_reg2hw_t reg2hw,
  input otbn_hw2reg_t hw2reg,
  input logic         done_i,

  input prim_mubi_pkg::mubi4_t idle_o_i,

  input logic otbn_dmem_scramble_key_req_busy_i,
  input logic otbn_imem_scramble_key_req_busy_i,

  input logic [7:0] status_q_i,
  input logic busy_secure_wipe,
  input logic [38:0] imem_rdata_bus,
  input logic [ExtWLEN-1:0] dmem_rdata_bus
);

  // Several of the internal signals that we snoop from the otbn module run "a cycle early". This
  // lets the design flop some outputs, but we need to do some converting here to get everything to
  // line up.
  logic rotating_keys, done;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rotating_keys <= 1'b0;
      done          <= 1'b0;
    end else begin
      rotating_keys <= otbn_dmem_scramble_key_req_busy_i | otbn_imem_scramble_key_req_busy_i;
      done          <= done_i;
    end
  end

  // Detect writes to CMD. They only take effect if we are in state IDLE
  logic cmd_operation, start_req, do_start;

  assign cmd_operation = reg2hw.cmd.q inside {otbn_pkg::CmdSecWipeImem,
                                              otbn_pkg::CmdSecWipeDmem,
                                              otbn_pkg::CmdExecute};

  assign start_req = reg2hw.cmd.qe && cmd_operation;

  assign do_start = start_req && (hw2reg.status.d == otbn_pkg::StatusIdle);

  // Track whether OTBN has completed its initial secure wipe.
  logic init_sec_wipe_done;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      init_sec_wipe_done <= 1'b0;
    end else begin
      if (~busy_secure_wipe) begin
        init_sec_wipe_done <= 1'b1;
      end
    end
  end

  // Our model of whether OTBN is running or not. We start on `do_start` once the initial secure
  // wipe is done, and we stop on `done`.
  logic running_qq, running_q, running_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running_q  <= 1'b1;
      running_qq <= 1'b1;
    end else begin
      running_q  <= running_d;
      running_qq <= running_q;
    end
  end
  assign running_d = do_start & init_sec_wipe_done ? 1'b1 : // set
                     done ? 1'b0 : // clear
                     ~init_sec_wipe_done & ~busy_secure_wipe ? 1'b0 : // clear
                     running_q; // keep

  // We should never see done when we're not already running. The converse assertion, that we never
  // see cmd_start when we are running, need not be true: the host can do that if it likes and OTBN
  // will ignore it. But we should never see do_start when we think we're running.
  `ASSERT(RunningIfDone_A, done |-> running_q)
  `ASSERT(IdleIfStart_A, do_start |-> !running_q)

  // Key rotation (used in the logic below) can delay the idle signal. This signal is flopped an
  // extra time to stay "busy" for an extra cycle, so we mirror that here.
  logic rotating_keys_q, keys_busy;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rotating_keys_q <= 1'b0;
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
  //  - If the STATUS register has value LOCKED then idle should be false if key rotation is busy
  //    (NotIdleIfLockedAndRotatingKeys_A) and idle should be true if neither key rotation nor
  //    secure wipe are busy (IdleIfLockedAndNotRotatingKeys_A).
  //
  //  - We should never start a new key request once STATUS has value LOCKED
  //    (NoStartKeyRotationWhenLocked_A)
  //
  //  - We should only have a key request in flight if we are either running (as tracked by
  //    start/done) or LOCKED (OnlyKeyRotationWhenRunningOrLocked_A)
  //
  //  - If STATUS has value LOCKED and no secure wipe is running, we should not think OTBN is
  //    running (NotRunningWhenLocked_A).

  `ASSERT(NotIdleIfRunning_A,
          running_q |-> ##[0:1] (idle_o_i == prim_mubi_pkg::MuBi4False))

  // TODO(#23903):
  //
  //    The logic here is to cope with a single cycle of surprising behaviour we are neither running
  //    nor locked but the idle_o signal is not high. This is probably a (minor) RTL bug. When it is
  //    fixed, we can strengthen this check again to disallow a the single cycle mismatch.
  logic running_or_locked;
  logic missing_idle_d, missing_idle_q;
  assign running_or_locked = running_qq ||
                             busy_secure_wipe ||
                             status_q_i == otbn_pkg::StatusLocked;
  assign missing_idle_d = !running_or_locked && (idle_o_i != prim_mubi_pkg::MuBi4True);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      missing_idle_q <= 1'b0;
    end else begin
      missing_idle_q <= missing_idle_d;
    end
  end

  `ASSERT(IdleIfNotRunningOrLocked_A, !(missing_idle_d && missing_idle_q))

  `ASSERT(NotIdleIfLockedAndRotatingKeys_A,
          ((status_q_i == otbn_pkg::StatusLocked) && keys_busy) |->
          (idle_o_i == prim_mubi_pkg::MuBi4False))

  `ASSERT(IdleIfLockedAndNotRotatingKeys_A,
          // `keys_busy` runs a cycle late compared to `busy_secure_wipe`.  Thus, depending on which
          // component causes the condition to become true, it can take one or two cycles for `idle`
          // to become true.
          ((status_q_i == otbn_pkg::StatusLocked) && !keys_busy && !busy_secure_wipe) |-> ##[1:2]
          (idle_o_i == prim_mubi_pkg::MuBi4True))

  `ASSERT(NoStartKeyRotationWhenLocked_A,
          (status_q_i == otbn_pkg::StatusLocked) |=> !$rose(keys_busy))

  `ASSERT(OnlyKeyRotationWhenRunningOrLocked_A,
          keys_busy |-> (running_q || (status_q_i == otbn_pkg::StatusLocked)))

  `ASSERT(NotRunningWhenLocked_A,
          (status_q_i == otbn_pkg::StatusLocked && !busy_secure_wipe) |->
          !running_d)

  // When OTBN locks bus read data integrity is forced to the correct value for 0 data (so reads to
  // a locked OTBN don't cause an integrity error). There is a small window where running_q is set
  // with status_q reporting 'StatusLocked'. So expected bus read data depends upon locked status
  // when running.
  `ASSERT(NoMemRdataWhenBusy_A,
    running_q && !(status_q_i == otbn_pkg::StatusBusySecWipeInt) |->
      ((status_q_i == otbn_pkg::StatusLocked) ?
      imem_rdata_bus == EccZeroWord && dmem_rdata_bus == EccWideZeroWord :
      imem_rdata_bus == 'b0 && dmem_rdata_bus == 'b0))


endmodule
