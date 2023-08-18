// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SYNTHESIS
`include "prim_assert.sv"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */

module otbn_core_model
  import otbn_pkg::*;
  import edn_pkg::*;
  import keymgr_pkg::otbn_key_req_t;
#(
  // The scope that contains the instruction and data memory (for DPI)
  parameter string MemScope = "",

  // Scope of an RTL OTBN implementation (for DPI). This should be give the scope for the top-level
  // of a real implementation running alongside. We will use it to check DMEM and register file
  // contents on completion of an operation.
  parameter string DesignScope = ""
)(
  input  logic               clk_i,
  input  logic               clk_edn_i,
  input  logic               rst_ni,
  input  logic               rst_edn_ni,

  input  logic [7:0]         cmd_i,    // CMD register for OTBN commands
  input  logic               cmd_en_i, // CMD register enable for OTBN commands

  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t lc_rma_req_i,

  output err_bits_t          err_bits_o, // updated when STATUS switches to idle

  input  edn_pkg::edn_rsp_t  edn_rnd_i, // EDN response interface for RND
  output logic               edn_rnd_o, // EDN request interface for RND
  input  logic               edn_rnd_cdc_done_i, // RND from EDN is valid (DUT perspective)

  input  edn_pkg::edn_rsp_t  edn_urnd_i, // EDN response interface for URND seed
  output logic               edn_urnd_o, // EDN request interface for URND seed
  input  logic               edn_urnd_cdc_done_i, // URND seed from EDN is valid (DUT perspective)

  input  logic           init_sec_wipe_done_i,

  input  logic           otp_key_cdc_done_i, // Scrambling key from OTP is valid (DUT perspective)

  output bit [7:0]       status_o,   // STATUS register
  output bit [31:0]      insn_cnt_o, // INSN_CNT register

  input keymgr_pkg::otbn_key_req_t keymgr_key_i,

  output bit             done_rr_o,

  output bit             err_o // something went wrong
);

`include "otbn_model_dpi.svh"

  // Create and destroy an object through which we can talk to the ISS.
  chandle model_handle;
  initial begin
    model_handle = otbn_model_init(MemScope, DesignScope);
    assert(model_handle != null);
  end
  final begin
    otbn_model_destroy(model_handle);
  end

  // A packed set of bits representing the state of the model. This gets assigned by DPI function
  // calls that need to update both whether we're running and also error flags at the same time. The
  // contents are magic simulation values, so get initialized before reset (to avoid stopping the
  // simulation before it even starts).
  int unsigned model_state = 0;

  // Extract particular bits of the model_state value.
  //
  //   [0]     running:      The ISS is currently running
  //   [1]     check_due:    The ISS needs to check results
  //   [2]     failed_step:  Something went wrong when trying to start or step the ISS.

  bit failed_step, check_due, running;
  assign {failed_step, check_due, running} = model_state[2:0];

  // Process incoming CMD command only when it is allowed to do so.
  logic [7:0]  cmd;

  assign cmd = cmd_en_i ? cmd_i : 8'h0;
  bit [7:0]  status_q;
  bit [31:0] insn_cnt_q;
  bit [31:0] raw_err_bits_q;
  bit [31:0] stop_pc_q;
  bit        rnd_req_start_q;

  bit unused_raw_err_bits;
  logic unused_edn_rsp_fips;

  logic lock_immediately_d, lock_immediately_q;

  // EDN RND Request Logic
  logic edn_rnd_req_q, edn_rnd_req_d;

  // Since RND is instantly set inside model we need to wait right until
  // it is also going to be written in RTL (which takes one cycle).
  logic edn_rnd_cdc_done_q;

  // The lc_escalate_en_i and lc_rma_req_i signals in the design go through a prim_lc_sync
  // which always injects exactly two cycles of delay (this is a synchroniser, not a CDC, so
  // its behaviour is easy to predict).
  // We model those delays in the SystemVerilog here, since it's much easier than handling it
  // in the Python.
  logic [2:0] escalate_fifo;
  logic [2:0] rma_req_fifo;
  logic [2:0] lc_mubi_err_fifo;
  logic       new_escalation;
  logic       new_rma_req;
  logic       new_lc_mubi_err;
  logic       valid_lc_rma_req;
  logic       valid_lc_esc_req;
  logic       valid_lc_mubi_err;
  logic       invalid_lc_rma_req;

  assign invalid_lc_rma_req = lc_ctrl_pkg::lc_tx_test_invalid(lc_rma_req_i);

  assign valid_lc_rma_req = lc_ctrl_pkg::lc_tx_test_true_strict(lc_rma_req_i);
  // Anything else than OFF is ON.
  assign valid_lc_esc_req = lc_ctrl_pkg::lc_tx_test_true_loose(lc_escalate_en_i);
  assign valid_lc_mubi_err = invalid_lc_rma_req;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      escalate_fifo <= '0;
      rma_req_fifo <= '0;
      lc_mubi_err_fifo <= '0;
    end else begin
      escalate_fifo <= {escalate_fifo[1:0], valid_lc_esc_req};
      rma_req_fifo <= {rma_req_fifo[1:0], valid_lc_rma_req};
      lc_mubi_err_fifo <= {lc_mubi_err_fifo[1:0], valid_lc_mubi_err};
    end
  end
  assign new_escalation = escalate_fifo[1] & ~escalate_fifo[2];
  assign new_rma_req = rma_req_fifo[1] & ~rma_req_fifo[2];
  assign new_lc_mubi_err = lc_mubi_err_fifo[1] & ~lc_mubi_err_fifo[2];

  assign lock_immediately_d = new_lc_mubi_err | lock_immediately_q;

  // RND Request starts if OTBN Model raises rnd_req_start while we are not
  // finishing up processing RND.
  assign edn_rnd_req_d = ~edn_rnd_cdc_done_q & (edn_rnd_req_q | rnd_req_start_q);

  assign edn_rnd_o = edn_rnd_req_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      edn_rnd_req_q <= 1'b0;
      edn_rnd_cdc_done_q <= 1'b0;
      lock_immediately_q <= 1'b0;
    end else begin
      edn_rnd_cdc_done_q <= edn_rnd_cdc_done_i;
      edn_rnd_req_q <= edn_rnd_req_d;
      lock_immediately_q <= lock_immediately_d;
    end
  end

  // EDN URND Seed Request Logic
  logic start_q, start_d;
  bit is_idle;

  assign start_d = (cmd == CmdExecute) & is_idle;
  assign is_idle = otbn_pkg::status_e'(status_o) == StatusIdle;

  // URND Reseeding is done twice as part of every secure wipe: once before the secure wipe and once
  // after a first wipe with random data.  A secure wipe happens after reset and when OTBN receives
  // the `EXECUTE` command.
  typedef enum logic [2:0] {
    OtbnCoreModelUrndStateReset,
    OtbnCoreModelUrndStateAwaitInitialAck,
    OtbnCoreModelUrndStateAwaitWipe,
    OtbnCoreModelUrndStateAwaitSecondAck,
    OtbnCoreModelUrndStateAwaitStart,
    OtbnCoreModelUrndStateAwaitPostStartAck,
    OtbnCoreModelUrndStateAwaitPostExecSecWipe
  } urnd_state_e;
  urnd_state_e urnd_state_q, urnd_state_d;

  localparam int unsigned WIPE_CYCLES = 67;
  typedef logic [$clog2(WIPE_CYCLES+1)-1:0] wipe_cyc_cnt_t;
  wipe_cyc_cnt_t wipe_cyc_cnt_q, wipe_cyc_cnt_d;

  always_comb begin
    edn_urnd_o     = 1'b0;
    urnd_state_d   = urnd_state_q;
    wipe_cyc_cnt_d = wipe_cyc_cnt_q;

    unique case (urnd_state_q)
      OtbnCoreModelUrndStateReset: begin
        urnd_state_d = OtbnCoreModelUrndStateAwaitInitialAck;
      end

      OtbnCoreModelUrndStateAwaitInitialAck: begin
        edn_urnd_o = 1'b1;
        if (edn_urnd_cdc_done_i) begin
          wipe_cyc_cnt_d = wipe_cyc_cnt_t'(WIPE_CYCLES);
          urnd_state_d   = OtbnCoreModelUrndStateAwaitWipe;
        end
      end

      OtbnCoreModelUrndStateAwaitWipe: begin
        wipe_cyc_cnt_d = wipe_cyc_cnt_q - 1;
        if (wipe_cyc_cnt_q == '0) begin
          edn_urnd_o   = 1'b1;
          urnd_state_d = OtbnCoreModelUrndStateAwaitSecondAck;
        end
      end

      OtbnCoreModelUrndStateAwaitSecondAck: begin
        edn_urnd_o = 1'b1;
        if (edn_urnd_cdc_done_i) begin
          urnd_state_d = OtbnCoreModelUrndStateAwaitStart;
        end
      end

      OtbnCoreModelUrndStateAwaitStart: begin
        if (start_q) begin
          urnd_state_d = OtbnCoreModelUrndStateAwaitPostStartAck;
        end
      end

      OtbnCoreModelUrndStateAwaitPostStartAck: begin
        edn_urnd_o = 1'b1;
        if (edn_urnd_cdc_done_i) begin
          urnd_state_d = OtbnCoreModelUrndStateAwaitPostExecSecWipe;
        end
      end

      OtbnCoreModelUrndStateAwaitPostExecSecWipe: begin
        if (status_q == StatusBusySecWipeInt) begin
          // This wipe is three clock cycles shorter, because it does starts directly after
          // execution and not directly after an URND reseed.
          wipe_cyc_cnt_d = wipe_cyc_cnt_t'(WIPE_CYCLES) - 3;
          urnd_state_d   = OtbnCoreModelUrndStateAwaitWipe;
        end
      end

      default: urnd_state_d = OtbnCoreModelUrndStateReset;
    endcase

    if (lock_immediately_q) begin
      urnd_state_d = OtbnCoreModelUrndStateReset;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_q            <= 1'b0;
      urnd_state_q       <= OtbnCoreModelUrndStateReset;
      wipe_cyc_cnt_q     <= '0;
    end else begin
      start_q        <= start_d;
      urnd_state_q   <= urnd_state_d;
      wipe_cyc_cnt_q <= wipe_cyc_cnt_d;
    end
  end

  // EDN Stepping is done with the EDN clock for also asserting the CDC measures in the design.
  logic failed_edn_flush, failed_rnd_step, failed_urnd_step;
  always_ff @(posedge clk_edn_i or negedge rst_edn_ni) begin
    if (!rst_edn_ni) begin
      failed_rnd_step <= 0;
      failed_urnd_step <= 0;
      failed_edn_flush <= (otbn_model_edn_flush(model_handle) != 0);
    end else begin
      if (edn_rnd_i.edn_ack) begin
        failed_rnd_step <= (otbn_model_edn_rnd_step(model_handle, edn_rnd_i.edn_bus,
                                                    ~edn_rnd_i.edn_fips) != 0);
      end
      if (edn_urnd_i.edn_ack) begin
        failed_urnd_step <= (otbn_model_edn_urnd_step(model_handle, edn_urnd_i.edn_bus) != 0);
      end
    end
  end

  // A "busy" counter. We'd like to avoid stepping the Python process on every cycle when there's
  // nothing going on (since it's rather expensive). But exactly modelling *when* we can safely
  // avoid doing this is rather awkward. So we do a conservative approximation. We know that some
  // events show there's stuff going on (the 'running' bit, a CDC completion, or a lifecycle
  // escalation signal). If these happen, we reset the counter. If it gets down to zero, we stop
  // stepping the model. This counter lets us "flush out" events for a few cycles without having to
  // model the timing too precisely on the SV side.
  logic [3:0] busy_counter_q, busy_counter_d;
  logic       reset_busy_counter, step_iss;
  // This bit can be set by a hierrachical component when ISS model should step for extra time.
  bit         wakeup_iss;

  initial begin
    wakeup_iss = 0;
  end

  assign reset_busy_counter = |{running, cmd_en_i, check_due, new_escalation, edn_rnd_cdc_done_i,
                                ~init_sec_wipe_done_i, wakeup_iss, new_rma_req};
  assign step_iss = reset_busy_counter || (busy_counter_q != 0);

  always_comb begin
    busy_counter_d = busy_counter_q;

    if (reset_busy_counter) begin
      busy_counter_d = 4'd10;
    end else if (busy_counter_q > 0) begin
      busy_counter_d = busy_counter_q - 4'd1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      busy_counter_q <= 0;
    end else begin
      busy_counter_q <= busy_counter_d;
    end
  end

  // Note: This can't be an always_ff block because we write to model_state here and also in an
  // initial block (see declaration of the variable above)
  bit failed_reset, failed_lc_escalate, failed_keymgr_value, failed_lc_rma_req;
  bit failed_urnd_cdc, failed_rnd_cdc, failed_otp_key_cdc;
  bit failed_initial_secure_wipe, initial_secure_wipe_started;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      failed_reset <= (otbn_model_reset(model_handle,
                                        status_q,
                                        insn_cnt_q,
                                        rnd_req_start_q,
                                        raw_err_bits_q,
                                        stop_pc_q)
                       != 0);
      failed_lc_escalate <= 0;
      failed_keymgr_value <= 0;
      failed_urnd_cdc <= 0;
      failed_rnd_cdc <= 0;
      failed_otp_key_cdc <= 0;
      failed_initial_secure_wipe <= 0;
      initial_secure_wipe_started <= 0;
      model_state <= 0;
    end else begin
      if (!initial_secure_wipe_started) begin
        failed_initial_secure_wipe <= (otbn_model_initial_secure_wipe(model_handle) != 0);
        initial_secure_wipe_started <= 1;
      end
      if (new_escalation) begin
        // Setting LIFECYCLE_ESCALATION bit
        failed_lc_escalate <= (otbn_model_send_err_escalation(model_handle,
                                                              32'd1 << 22,
                                                              1'b0)
                               != 0);
      end
      if (new_lc_mubi_err) begin
        // Setting BAD_INTERNAL_STATE bit
        failed_lc_escalate <= (otbn_model_send_err_escalation(model_handle,
                                                              32'd1 << 20,
                                                              1'b1)
                               != 0);
      end
      if (new_rma_req) begin
        failed_lc_rma_req <= (otbn_model_send_rma_req(model_handle) != 0);
      end
      if (!$stable(keymgr_key_i) || $rose(rst_ni)) begin
        failed_keymgr_value <= (otbn_model_set_keymgr_value(model_handle,
                                                            keymgr_key_i.key[0],
                                                            keymgr_key_i.key[1],
                                                            keymgr_key_i.valid) != 0);
      end
      if (edn_urnd_cdc_done_i) begin
        failed_urnd_cdc <= (otbn_model_urnd_cdc_done(model_handle) != 0);
      end
      if (edn_rnd_cdc_done_i) begin
        failed_rnd_cdc <= (otbn_model_rnd_cdc_done(model_handle) != 0);
      end
      if (otp_key_cdc_done_i) begin
        failed_otp_key_cdc <= (otbn_model_otp_key_cdc_done(model_handle) != 0);
      end
      if (step_iss) begin
        model_state <= otbn_model_step(model_handle,
                                       model_state,
                                       cmd,
                                       status_q,
                                       insn_cnt_q,
                                       rnd_req_start_q,
                                       raw_err_bits_q,
                                       stop_pc_q);
      end
    end
  end

  // If a check is requested, run it on the following negedge. This guarantees that both the ISS and
  // RTL are "at the end" of a cycle.
  logic check_mismatch_d, check_mismatch_q;
  bit   failed_check;
  always_ff @(negedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      failed_check <= 0;
      check_mismatch_q <= 0;
    end else begin
      if (check_due) begin
        failed_check <= (otbn_model_check(model_handle, check_mismatch_d) == 0);
        check_mismatch_q <= check_mismatch_d;
      end
    end
  end

  // Assertion to ensure that keymgr key valid is never unknown.
  `ASSERT_KNOWN(KeyValidIsKnownChk_A, keymgr_key_i.valid)
  // Assertion to ensure that keymgr key values are never unknown if valid is high.
  `ASSERT_KNOWN_IF(KeyIsKnownChk_A, {keymgr_key_i.key[0], keymgr_key_i.key[1]}, keymgr_key_i.valid)
  assign unused_raw_err_bits = ^raw_err_bits_q[31:$bits(err_bits_t)];
  assign unused_edn_rsp_fips = edn_urnd_i.edn_fips;

  assign err_bits_o = raw_err_bits_q[$bits(err_bits_t)-1:0];

  assign status_o = status_q;
  assign insn_cnt_o = insn_cnt_q;

  // TODO: This bind is by module, rather than by instance, because I couldn't get the by-instance
  // syntax plus upwards name referencing to work with Verilator. Obviously, this won't work with
  // multiple OTBN instances, so it would be nice to get it right.
  bind otbn_rf_base_ff otbn_rf_snooper_if #(
    .Width           (BaseIntgWidth),
    .Depth           (NGpr),
    .IntegrityEnabled(1)
  ) u_snooper (
    .rf (rf_reg)
  );

  bind otbn_rf_bignum_ff otbn_rf_snooper_if #(
    .Width           (ExtWLEN),
    .Depth           (NWdr),
    .IntegrityEnabled(1)
  ) u_snooper (
    .rf (rf)
  );

  bind otbn_rf_base otbn_stack_snooper_if #(.StackIntgWidth(39), .StackWidth(32), .StackDepth(8))
    u_call_stack_snooper (
      .stack_storage(u_call_stack.stack_storage),
      .stack_wr_ptr_q(u_call_stack.stack_wr_ptr)
    );

  assign err_o = |{failed_step, failed_check, check_mismatch_q,
                   failed_reset, failed_lc_escalate, failed_keymgr_value,
                   failed_edn_flush, failed_rnd_step, failed_urnd_step,
                   failed_urnd_cdc, failed_rnd_cdc, failed_otp_key_cdc,
                   failed_initial_secure_wipe, failed_lc_rma_req};

  // Derive a "done" signal. This should trigger for a single cycle when OTBN finishes its work.
  // It's analogous to the done_o signal on otbn_core, but this signal is delayed by a single cycle
  // (hence its name is done_r_o).
  bit otbn_model_busy, otbn_model_busy_r;
  assign otbn_model_busy = !(status_q inside {StatusIdle, StatusLocked}) & init_sec_wipe_done_i;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      otbn_model_busy_r <= 1'b0;
    end else begin
      otbn_model_busy_r <= otbn_model_busy;
    end
  end
  assign done_rr_o = otbn_model_busy_r & ~otbn_model_busy;

  // Make stop_pc available over DPI. This is handy for Verilator simulations (where the top-level
  // is in C++).
  export "DPI-C" function otbn_core_get_stop_pc;
  function automatic int otbn_core_get_stop_pc();
    return stop_pc_q;
  endfunction

endmodule
`endif // SYNTHESIS
