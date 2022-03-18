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
  #(
  // Enable internal secure wipe
  parameter bit                SecWipeEn  = 1'b0
)(
  input  logic clk_i,
  input  logic rst_ni,

  input  logic start_i,

  output logic controller_start_o,

  output logic urnd_reseed_req_o,
  input  logic urnd_reseed_busy_i,
  output logic urnd_advance_o,

  input   logic start_secure_wipe_i,
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
  output logic state_error_o
);
  otbn_start_stop_state_e state_q, state_d;

  logic addr_cnt_inc;
  logic [4:0] addr_cnt_q, addr_cnt_d;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateStartStopWidth-1:0] state_raw_q;
  assign state_q = otbn_start_stop_state_e'(state_raw_q);
  prim_sparse_fsm_flop #(
    .StateEnumT(otbn_start_stop_state_e),
    .Width(StateStartStopWidth),
    .ResetValue(StateStartStopWidth'(OtbnStartStopStateHalt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d     ),
    .state_o ( state_raw_q )
  );

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
    secure_wipe_running_o  = 1'b0;
    state_error_o          = 1'b0;

    unique case (state_q)
      OtbnStartStopStateHalt: begin
        if (start_i) begin
          urnd_reseed_req_o = 1'b1;
          ispr_init_o       = 1'b1;
          state_reset_o     = 1'b1;
          state_d           = OtbnStartStopStateUrndRefresh;
        end
      end
      OtbnStartStopStateUrndRefresh: begin
        if (!urnd_reseed_busy_i) begin
          state_d     = OtbnStartStopStateRunning;
        end
      end
      OtbnStartStopStateRunning: begin
        urnd_advance_o = 1'b1;
        if (start_secure_wipe_i) begin
          if (SecWipeEn) begin
            state_d = OtbnStartStopSecureWipeWdrUrnd;
          end
          else begin
            state_d = OtbnStartStopSecureWipeComplete;
          end
        end
      end
      // Writing random numbers to the wide data registers.
       OtbnStartStopSecureWipeWdrUrnd: begin
        urnd_advance_o        = 1'b1;
        addr_cnt_inc          = 1'b1;
        sec_wipe_wdr_o        = 1'b1;
        sec_wipe_wdr_urnd_o   = 1'b1;
        secure_wipe_running_o = 1'b1;
        if (addr_cnt_q == 5'b11111) begin
          state_d = OtbnStartStopSecureWipeAccModBaseUrnd;
        end
      end
      // Writing random numbers to the accumulator, modulus and the base registers.
      // addr_cnt_q wraps around to 0 when first moving to this state, and we need to
      // supress writes to the zero register and the call stack.
       OtbnStartStopSecureWipeAccModBaseUrnd: begin
        secure_wipe_running_o = 1'b1;
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
        secure_wipe_running_o = 1'b1;
        sec_wipe_zero_o       = (addr_cnt_q == 5'b00000);
        sec_wipe_wdr_o        = 1'b1;
        sec_wipe_base_o       = (addr_cnt_q > 5'b00001);
        addr_cnt_inc = 1'b1;
        if (addr_cnt_q == 5'b11111) begin
          state_d = OtbnStartStopSecureWipeComplete;
        end
      end
       OtbnStartStopSecureWipeComplete: begin
        urnd_advance_o = 1'b1;
        secure_wipe_running_o = 1'b1;
        state_d = OtbnStartStopStateHalt;
      end
      default: begin
        state_error_o = 1'b1;
      end
    endcase
  end

  // Logic separate from main FSM code to avoid false combinational loop warning from verilator
  assign controller_start_o = (state_q == OtbnStartStopStateUrndRefresh) & !urnd_reseed_busy_i;

  assign done_o = (state_q == OtbnStartStopSecureWipeComplete);

  assign addr_cnt_d = addr_cnt_inc ? (addr_cnt_q + 5'd1) : 5'd0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_q <= 5'd0;
    end else
      addr_cnt_q <= addr_cnt_d;
  end

  assign sec_wipe_addr_o = addr_cnt_q;

  `ASSERT(StartStopStateValid,
      state_q inside {OtbnStartStopStateHalt,
                      OtbnStartStopStateUrndRefresh,
                      OtbnStartStopStateRunning,
                      OtbnStartStopSecureWipeWdrUrnd,
                      OtbnStartStopSecureWipeAccModBaseUrnd,
                      OtbnStartStopSecureWipeAllZero,
                      OtbnStartStopSecureWipeComplete})

endmodule
