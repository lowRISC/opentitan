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
(
  input  logic clk_i,
  input  logic rst_ni,

  input  logic  start_i,
  input mubi4_t escalate_en_i,

  output logic controller_start_o,

  output logic urnd_reseed_req_o,
  input  logic urnd_reseed_ack_i,
  output logic urnd_advance_o,

  input   logic secure_wipe_req_i,
  output  logic secure_wipe_ack_o,
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

  otbn_start_stop_state_e state_q, state_d;

  logic addr_cnt_inc;
  logic [4:0] addr_cnt_q, addr_cnt_d;

  // There are two ways in which the start/stop controller can be told to stop. Either
  // secure_wipe_req_i comes from the controller (which means "I've run some instructions and I've
  // hit an ECALL or error"). Or escalate_en_i can be asserted (which means "Someone else has told
  // us to stop immediately"). If running, both can be true at once.
  //
  // An escalation signal gets latched into should_lock. If we were running some instructions, we'll
  // go through the secure wipe process, but we'll see the should_lock_q signal when done and go
  // into the local locked state.
  // SEC_CM: CONTROLLER.FSM.GLOBAL_ESC
  logic esc_request, should_lock_d, should_lock_q, stop;
  assign esc_request   = mubi4_test_true_loose(escalate_en_i);
  assign stop          = esc_request | secure_wipe_req_i;
  assign should_lock_d = should_lock_q | esc_request;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      should_lock_q <= 1'b0;
    end else begin
      should_lock_q <= should_lock_d;
    end
  end

  // SEC_CM: START_STOP_CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q,
      otbn_start_stop_state_e, OtbnStartStopStateHalt)

  always_comb begin
    urnd_reseed_req_o      = 1'b0;
    urnd_advance_o         = 1'b0;
    state_d                = state_q;
    ispr_init_o            = 1'b0;
    state_reset_o          = 1'b0;
    sec_wipe_wdr_o         = 1'b0;
    sec_wipe_wdr_urnd_o    = 1'b0;
    sec_wipe_base_o        = 1'b0;
    sec_wipe_base_urnd_o   = 1'b0;
    sec_wipe_acc_urnd_o    = 1'b0;
    sec_wipe_mod_urnd_o    = 1'b0;
    sec_wipe_zero_o        = 1'b0;
    addr_cnt_inc           = 1'b0;
    fatal_error_o          = 1'b0;
    secure_wipe_ack_o      = 1'b0;

    unique case (state_q)
      OtbnStartStopStateHalt: begin
        if (stop) begin
          state_d = OtbnStartStopStateLocked;
        end else if (start_i) begin
          urnd_reseed_req_o = 1'b1;
          ispr_init_o       = 1'b1;
          state_reset_o     = 1'b1;
          state_d           = OtbnStartStopStateUrndRefresh;
        end
      end
      OtbnStartStopStateUrndRefresh: begin
        urnd_reseed_req_o = 1'b1;
        if (stop) begin
          state_d = OtbnStartStopStateLocked;
        end else if (urnd_reseed_ack_i) begin
          state_d     = OtbnStartStopStateRunning;
        end
      end
      OtbnStartStopStateRunning: begin
        urnd_advance_o = 1'b1;
        if (stop) begin
          state_d = OtbnStartStopSecureWipeWdrUrnd;
        end
      end
      // Writing random numbers to the wide data registers.
       OtbnStartStopSecureWipeWdrUrnd: begin
        urnd_advance_o        = 1'b1;
        addr_cnt_inc          = 1'b1;
        sec_wipe_wdr_o        = 1'b1;
        sec_wipe_wdr_urnd_o   = 1'b1;
        if (addr_cnt_q == 5'b11111) begin
          state_d = OtbnStartStopSecureWipeAccModBaseUrnd;
        end
      end
      // Writing random numbers to the accumulator, modulus and the base registers.
      // addr_cnt_q wraps around to 0 when first moving to this state, and we need to
      // supress writes to the zero register and the call stack.
       OtbnStartStopSecureWipeAccModBaseUrnd: begin
        urnd_advance_o        = 1'b1;
        addr_cnt_inc          = 1'b1;
        // The first two clock cycles are used to write random data to accumulator and modulus.
        sec_wipe_acc_urnd_o   = (addr_cnt_q == 5'b00000);
        sec_wipe_mod_urnd_o   = (addr_cnt_q == 5'b00001);
        // Supress writes to the zero register and the call stack.
        sec_wipe_base_o       = (addr_cnt_q > 5'b00001);
        sec_wipe_base_urnd_o  = (addr_cnt_q > 5'b00001);
        if (addr_cnt_q == 5'b11111) begin
          state_d = OtbnStartStopSecureWipeAllZero;
        end
      end
      // Writing zeros to the accumulator, modulus and the registers.
      // Resetting stack
       OtbnStartStopSecureWipeAllZero: begin
        sec_wipe_zero_o       = (addr_cnt_q == 5'b00000);
        sec_wipe_wdr_o        = 1'b1;
        sec_wipe_base_o       = (addr_cnt_q > 5'b00001);
        addr_cnt_inc = 1'b1;
        if (addr_cnt_q == 5'b11111) begin
          state_d = OtbnStartStopSecureWipeComplete;
          secure_wipe_ack_o = 1'b1;
        end
      end
      OtbnStartStopSecureWipeComplete: begin
        urnd_advance_o = 1'b1;
        state_d = should_lock_d ? OtbnStartStopStateLocked : OtbnStartStopStateHalt;
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
        fatal_error_o = 1'b1;
        state_d = OtbnStartStopStateLocked;
      end
    endcase

    if (urnd_reseed_ack_i && (state_q != OtbnStartStopStateUrndRefresh)) begin
      // We should never receive an ACK from URND when we're not refreshing the URND. Signal an
      // error if we see a stray ACK and lock the FSM.
      fatal_error_o = 1'b1;
      state_d       = OtbnStartStopStateLocked;
    end
  end

  // Logic separate from main FSM code to avoid false combinational loop warning from verilator
  assign controller_start_o = (state_q == OtbnStartStopStateUrndRefresh) & urnd_reseed_ack_i;

  assign done_o = ((state_q == OtbnStartStopSecureWipeComplete) ||
                   (stop && (state_q == OtbnStartStopStateUrndRefresh)));

  assign addr_cnt_d = addr_cnt_inc ? (addr_cnt_q + 5'd1) : 5'd0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_q <= 5'd0;
    end else
      addr_cnt_q <= addr_cnt_d;
  end

  assign sec_wipe_addr_o = addr_cnt_q;

  `ASSERT(StartStopStateValid_A,
      state_q inside {OtbnStartStopStateHalt,
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
