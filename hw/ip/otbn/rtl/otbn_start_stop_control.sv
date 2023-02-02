// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * State machine to handle actions that occur around the start and stop of OTBN.
 *
 * This recieves the start signals from the top-level and passes them on to the
 * controller to begin execution when pre-start actions have finished.
 *
 * pre-start actions:
 *  - Seed LFSR for URND
 *
 * post-stop actions:
 *  - Internal Secure Wipe
 *    -Delete WDRs
 *    -Delete Base registers
 *    -Delete Accumulator
 *    -Delete Modulus
 *    -Reset stack
 */

`include "prim_assert.sv"

module otbn_start_stop_control
  import otbn_pkg::*;
  import prim_mubi_pkg::*;
#(
  // Disable URND advance when not in use. Useful for SCA only.
  parameter bit SecMuteUrnd = 1'b0,
  // Skip URND re-seed at the start of the operation. Useful for SCA only.
  parameter bit SecSkipUrndReseedAtStart = 1'b0
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic   start_i,
  input  mubi4_t escalate_en_i,
  input  mubi4_t rma_req_i,
  output mubi4_t rma_ack_o,

  output logic controller_start_o,

  output logic urnd_reseed_req_o,
  input  logic urnd_reseed_ack_i,
  output logic urnd_reseed_err_o,
  output logic urnd_advance_o,

  input   logic secure_wipe_req_i,
  output  logic secure_wipe_ack_o,
  output  logic secure_wipe_running_o,
  output  logic done_o,

  output logic       sec_wipe_wdr_o,
  output logic       sec_wipe_wdr_urnd_o,
  output logic       sec_wipe_base_o,
  output logic       sec_wipe_base_urnd_o,
  output logic [4:0] sec_wipe_addr_o,

  output logic sec_wipe_acc_urnd_o,
  output logic sec_wipe_mod_urnd_o,
  output logic sec_wipe_zero_o,

  output logic ispr_init_o,
  output logic state_reset_o,
  output logic fatal_error_o
);

  import otbn_pkg::*;

  // Create lint errors to reduce the risk of accidentally enabling these features.
  `ASSERT_STATIC_LINT_ERROR(OtbnSecMuteUrndNonDefault, SecMuteUrnd == 0)
  `ASSERT_STATIC_LINT_ERROR(OtbnSecSkipUrndReseedAtStartNonDefault, SecSkipUrndReseedAtStart == 0)

  otbn_start_stop_state_e state_q, state_d;
  logic init_sec_wipe_done_q, init_sec_wipe_done_d;
  mubi4_t wipe_after_urnd_refresh_q, wipe_after_urnd_refresh_d;
  mubi4_t rma_ack_d, rma_ack_q;
  logic state_error_q, state_error_d;
  logic mubi_err_q, mubi_err_d;
  logic urnd_reseed_err_q, urnd_reseed_err_d;
  logic secure_wipe_error_q, secure_wipe_error_d;
  logic skip_reseed_q;

  logic addr_cnt_inc;
  logic [5:0] addr_cnt_q, addr_cnt_d;

  logic spurious_urnd_ack_error;
  logic spurious_secure_wipe_req, dropped_secure_wipe_req;

  // There are three ways in which the start/stop controller can be told to stop.
  // 1. secure_wipe_req_i comes from the controller (which means "I've run some instructions and
  //    I've hit an ECALL or error").
  // 2. escalate_en_i can be asserted (which means "Someone else has told us to stop immediately").
  // 3. rma_req_i can be asserted (which means "Lifecycle wants to transition to the RMA state").
  // If running, all three can be true at once.
  //
  // An escalation signal as well as RMA requests get latched into should_lock. We'll then go
  // through the secure wipe process (unless we weren't running any instructions in case of an
  // escalation). We'll see the should_lock_q signal when done and go into the local locked
  // state. If necessary, the RMA request is acknowledged upon secure wipe completion.

  // SEC_CM: CONTROLLER.FSM.GLOBAL_ESC
  logic esc_request, rma_request, should_lock_d, should_lock_q, stop;
  assign esc_request   = mubi4_test_true_loose(escalate_en_i);
  assign rma_request   = mubi4_test_true_strict(rma_req_i);
  assign stop          = esc_request | rma_request | secure_wipe_req_i;
  assign should_lock_d = should_lock_q | esc_request | rma_request;

  // Only if SecSkipUrndReseedAtStart is set, the controller start pulse is sent
  // one cycle after leaving the Halt state.
  if (SecSkipUrndReseedAtStart) begin: gen_skip_reseed
    logic skip_reseed_d;

    assign skip_reseed_d = ((state_q == OtbnStartStopStateHalt) & start_i & ~stop);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        skip_reseed_q <= 1'b0;
      end else begin
        skip_reseed_q <= skip_reseed_d;
      end
    end
  end else begin: gen_reseed
    assign skip_reseed_q = 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      should_lock_q <= 1'b0;
    end else begin
      should_lock_q <= should_lock_d;
    end
  end

  prim_mubi4_sender #(
    .AsyncOn(1'b1),
    .EnSecBuf(1'b1),
    .ResetValue(prim_mubi_pkg::MuBi4False)
  ) u_prim_mubi4_sender_rma_ack (
    .clk_i,
    .rst_ni,
    .mubi_i(rma_ack_d),
    .mubi_o(rma_ack_q)
  );

  logic allow_secure_wipe, expect_secure_wipe;

  // SEC_CM: START_STOP_CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q,
      otbn_start_stop_state_e, OtbnStartStopStateInitial)

  always_comb begin
    urnd_reseed_req_o         = 1'b0;
    urnd_advance_o            = 1'b0;
    state_d                   = state_q;
    ispr_init_o               = 1'b0;
    state_reset_o             = 1'b0;
    sec_wipe_wdr_o            = 1'b0;
    sec_wipe_wdr_urnd_o       = 1'b0;
    sec_wipe_base_o           = 1'b0;
    sec_wipe_base_urnd_o      = 1'b0;
    sec_wipe_acc_urnd_o       = 1'b0;
    sec_wipe_mod_urnd_o       = 1'b0;
    sec_wipe_zero_o           = 1'b0;
    addr_cnt_inc              = 1'b0;
    secure_wipe_ack_o         = 1'b0;
    secure_wipe_running_o     = 1'b0;
    state_error_d             = state_error_q;
    allow_secure_wipe         = 1'b0;
    expect_secure_wipe        = 1'b0;
    spurious_urnd_ack_error   = 1'b0;
    wipe_after_urnd_refresh_d = wipe_after_urnd_refresh_q;
    rma_ack_d                 = rma_ack_q;
    mubi_err_d                = mubi_err_q;

    unique case (state_q)
      OtbnStartStopStateInitial: begin
        secure_wipe_running_o = 1'b1;
        urnd_reseed_req_o     = 1'b1;
        if (urnd_reseed_ack_i) begin
          urnd_advance_o = 1'b1;
          state_d        = OtbnStartStopSecureWipeWdrUrnd;
        end
      end
      OtbnStartStopStateHalt: begin
        if (stop && !rma_request) begin
          state_d = OtbnStartStopStateLocked;
        end else if (start_i || rma_request) begin
          urnd_reseed_req_o = ~SecSkipUrndReseedAtStart | rma_request;
          ispr_init_o       = 1'b1;
          state_reset_o     = 1'b1;
          state_d           = OtbnStartStopStateUrndRefresh;
        end
      end
      OtbnStartStopStateUrndRefresh: begin
        urnd_reseed_req_o = ~skip_reseed_q;
        if (stop) begin
          if (mubi4_test_false_strict(wipe_after_urnd_refresh_q) && !rma_request) begin
            // We are told to stop and don't have to wipe after the current URND refresh is ack'd,
            // so we lock immediately.
            state_d = OtbnStartStopStateLocked;
          end else begin
            // We are told to stop but should wipe after the current URND refresh is ack'd, so we
            // wait for the ACK and then do a secure wipe.
            allow_secure_wipe     = 1'b1;
            expect_secure_wipe    = 1'b1;
            secure_wipe_running_o = 1'b1;
            if (urnd_reseed_ack_i) begin
              state_d = OtbnStartStopSecureWipeWdrUrnd;
            end
          end
        end else begin
          if (mubi4_test_false_strict(wipe_after_urnd_refresh_q)) begin
            // We are not stopping and we don't have to wipe after the current URND refresh is
            // ack'd, so we wait for the ACK and then start executing.
            if (urnd_reseed_ack_i || skip_reseed_q) begin
              state_d = OtbnStartStopStateRunning;
            end
          end else begin
            // We are not stopping but should wipe after the current URND refresh is ack'd, so we
            // wait for the ACK and then do a secure wipe.
            allow_secure_wipe     = 1'b1;
            expect_secure_wipe    = 1'b1;
            secure_wipe_running_o = 1'b1;
            if (urnd_reseed_ack_i) begin
              state_d = OtbnStartStopSecureWipeWdrUrnd;
            end
          end
        end
      end
      OtbnStartStopStateRunning: begin
        urnd_advance_o    = ~SecMuteUrnd;
        allow_secure_wipe = 1'b1;

        if (stop) begin
          state_d = OtbnStartStopSecureWipeWdrUrnd;
        end
      end
      // SEC_CM: DATA_REG_SW.SEC_WIPE
      // Writing random numbers to the wide data registers.
       OtbnStartStopSecureWipeWdrUrnd: begin
        urnd_advance_o        = 1'b1;
        addr_cnt_inc          = 1'b1;
        sec_wipe_wdr_o        = 1'b1;
        sec_wipe_wdr_urnd_o   = 1'b1;
        allow_secure_wipe     = 1'b1;
        expect_secure_wipe    = 1'b1;
        secure_wipe_running_o = 1'b1;

        // Count one extra cycle when wiping the WDR, because the wipe signals to the WDR
        // (`sec_wipe_wdr_o` and `sec_wipe_wdr_urnd_o`) are flopped once but the wipe signals to the
        // ACC register, which is wiped directly after the last WDR, are not.  If we would not count
        // this extra cycle, the last WDR and the ACC register would be wiped simultaneously and
        // thus with the same random value.
        if (addr_cnt_q == 6'b100000) begin
          // Reset `addr_cnt` on the transition out of this state.
          addr_cnt_inc = 1'b0;
          // The following two signals are flopped once before they reach the FSM, so clear them one
          // cycle early here.
          sec_wipe_wdr_o      = 1'b0;
          sec_wipe_wdr_urnd_o = 1'b0;
          state_d = OtbnStartStopSecureWipeAccModBaseUrnd;
        end
      end
      // Writing random numbers to the accumulator, modulus and the base registers.
      // addr_cnt_q wraps around to 0 when first moving to this state, and we need to
      // supress writes to the zero register and the call stack.
       OtbnStartStopSecureWipeAccModBaseUrnd: begin
        urnd_advance_o        = 1'b1;
        addr_cnt_inc          = 1'b1;
        allow_secure_wipe     = 1'b1;
        expect_secure_wipe    = 1'b1;
        secure_wipe_running_o = 1'b1;
        // The first two clock cycles are used to write random data to accumulator and modulus.
        sec_wipe_acc_urnd_o   = (addr_cnt_q == 6'b000000);
        sec_wipe_mod_urnd_o   = (addr_cnt_q == 6'b000001);
        // Supress writes to the zero register and the call stack.
        sec_wipe_base_o       = (addr_cnt_q > 6'b000001);
        sec_wipe_base_urnd_o  = (addr_cnt_q > 6'b000001);
        if (addr_cnt_q == 6'b011111) begin
          state_d = OtbnStartStopSecureWipeAllZero;
        end
      end
      // Writing zeros to the CSRs and reset the stack. The other registers are intentionally not
      // overwritten with zero.
       OtbnStartStopSecureWipeAllZero: begin
        sec_wipe_zero_o       = 1'b1;
        allow_secure_wipe     = 1'b1;
        expect_secure_wipe    = 1'b1;
        secure_wipe_running_o = 1'b1;

        // Leave this state after a single cycle, which is sufficient to reset the CSRs and the
        // stack.
        if (mubi4_test_false_strict(wipe_after_urnd_refresh_q)) begin
          // This is the first round of wiping with random numbers, refresh URND and do a second
          // round.
          state_d = OtbnStartStopStateUrndRefresh;
          wipe_after_urnd_refresh_d = MuBi4True;
        end else begin
          // This is the second round of wiping with random numbers, so the secure wipe is
          // complete.
          state_d = OtbnStartStopSecureWipeComplete;
          secure_wipe_ack_o = 1'b1;
        end
      end
      OtbnStartStopSecureWipeComplete: begin
        urnd_advance_o = 1'b1;
        rma_ack_d = rma_req_i;
        state_d = should_lock_d ? OtbnStartStopStateLocked : OtbnStartStopStateHalt;
        wipe_after_urnd_refresh_d = MuBi4False;
      end
      OtbnStartStopStateLocked: begin
        // SEC_CM: START_STOP_CTRL.FSM.GLOBAL_ESC
        // SEC_CM: START_STOP_CTRL.FSM.LOCAL_ESC
        //
        // Terminal state. This is either accessed by glitching state_q (and going through the
        // default case below) or by getting an escalation signal
      end
      default: begin
        // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
        state_error_d = 1'b1;
        rma_ack_d = MuBi4False;
        state_d = OtbnStartStopStateLocked;
      end
    endcase

    if (urnd_reseed_ack_i &&
        !(state_q inside {OtbnStartStopStateInitial, OtbnStartStopStateUrndRefresh})) begin
      // We should never receive an ACK from URND when we're not refreshing the URND. Signal an
      // error if we see a stray ACK and lock the FSM.
      spurious_urnd_ack_error = 1'b1;
      state_d                 = OtbnStartStopStateLocked;
    end

    // If the MuBi signals take on invalid values, something bad is happening. Put them back to
    // a safe value (if possible) and signal an error.
    if (mubi4_test_invalid(escalate_en_i)) begin
      mubi_err_d = 1'b1;
      state_d = OtbnStartStopStateLocked;
    end
    if (mubi4_test_invalid(rma_req_i)) begin
      mubi_err_d = 1'b1;
      state_d = OtbnStartStopStateLocked;
    end
    if (mubi4_test_invalid(wipe_after_urnd_refresh_q)) begin
      wipe_after_urnd_refresh_d = MuBi4False;
      mubi_err_d = 1'b1;
      state_d = OtbnStartStopStateLocked;
    end
    if (mubi4_test_invalid(rma_ack_q)) begin
      rma_ack_d = MuBi4False;
      mubi_err_d = 1'b1;
      state_d = OtbnStartStopStateLocked;
    end
  end

  // Latch initial secure wipe done.
  assign init_sec_wipe_done_d = (state_q == OtbnStartStopSecureWipeComplete) ? 1'b1 : // set
                                init_sec_wipe_done_q; // keep

  // Logic separate from main FSM code to avoid false combinational loop warning from verilator
  assign controller_start_o =
    // The controller start pulse is fired when finishing the initial URND reseed.
    ((state_q == OtbnStartStopStateUrndRefresh) & (urnd_reseed_ack_i | skip_reseed_q) &
      mubi4_test_false_strict(wipe_after_urnd_refresh_q));

  assign done_o = ((state_q == OtbnStartStopSecureWipeComplete && init_sec_wipe_done_q) ||
                   (stop && (state_q == OtbnStartStopStateUrndRefresh) &&
                    mubi4_test_false_strict(wipe_after_urnd_refresh_q)) ||
                   (spurious_urnd_ack_error && !(state_q inside {OtbnStartStopStateHalt,
                                                                 OtbnStartStopStateLocked}) &&
                    init_sec_wipe_done_q) || (mubi_err_d && !mubi_err_q));

  assign addr_cnt_d = addr_cnt_inc ? (addr_cnt_q + 6'd1) : 6'd0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_q           <= 6'd0;
      init_sec_wipe_done_q <= 1'b0;
    end else begin
      addr_cnt_q           <= addr_cnt_d;
      init_sec_wipe_done_q <= init_sec_wipe_done_d;
    end
  end

  prim_mubi4_sender #(
    .AsyncOn(1),
    .ResetValue(MuBi4False)
  ) u_wipe_after_urnd_refresh_flop (
    .clk_i,
    .rst_ni,
    .mubi_i(wipe_after_urnd_refresh_d),
    .mubi_o(wipe_after_urnd_refresh_q)
  );

  // Clip the secure wipe address to [0..31].  This is safe because the wipe enable signals are
  // never set when the counter exceeds 5 bit, which we assert below.
  assign sec_wipe_addr_o = addr_cnt_q[4:0];
  `ASSERT(NoSecWipeAbove32Bit_A, addr_cnt_q[5] |-> (!sec_wipe_wdr_o && !sec_wipe_acc_urnd_o))

  // A check for spurious or dropped secure wipe requests.
  // We only expect to start a secure wipe when running.
  assign spurious_secure_wipe_req = secure_wipe_req_i & ~allow_secure_wipe;
  // Once we've started a secure wipe, the controller should not drop the request until we tell it
  // we're done. This does not apply for the *initial* secure wipe, though, which is controlled by
  // this module rather than the controller.
  assign dropped_secure_wipe_req  = expect_secure_wipe & init_sec_wipe_done_d & ~secure_wipe_req_i;

  // Delay the "glitch req/ack" error signal by a cycle. Otherwise, you end up with a combinatorial
  // loop through the escalation signal that our fatal_error_o causes otbn_core to pass to the
  // controller.
  assign secure_wipe_error_d = spurious_secure_wipe_req | dropped_secure_wipe_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_error_q       <= 1'b0;
      mubi_err_q          <= 1'b0;
      secure_wipe_error_q <= 1'b0;
      urnd_reseed_err_q   <= 1'b0;
    end else begin
      state_error_q       <= state_error_d;
      mubi_err_q          <= mubi_err_d;
      secure_wipe_error_q <= secure_wipe_error_d;
      urnd_reseed_err_q   <= urnd_reseed_err_d;
    end
  end

  assign urnd_reseed_err_d = spurious_urnd_ack_error ? 1'b1 // set
                                                     : urnd_reseed_err_q; // hold
  assign urnd_reseed_err_o = urnd_reseed_err_d;

  assign fatal_error_o = urnd_reseed_err_o | state_error_d | secure_wipe_error_q | mubi_err_q;

  assign rma_ack_o = rma_ack_q;

  `ASSERT(StartStopStateValid_A,
      state_q inside {OtbnStartStopStateInitial,
                      OtbnStartStopStateHalt,
                      OtbnStartStopStateUrndRefresh,
                      OtbnStartStopStateRunning,
                      OtbnStartStopSecureWipeWdrUrnd,
                      OtbnStartStopSecureWipeAccModBaseUrnd,
                      OtbnStartStopSecureWipeAllZero,
                      OtbnStartStopSecureWipeComplete,
                      OtbnStartStopStateLocked})

  `ASSERT(StartSecureWipeImpliesRunning_A,
          $rose(secure_wipe_req_i) |-> (state_q == OtbnStartStopStateRunning))

endmodule
