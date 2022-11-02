// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES counter FSM for CTR mode

`include "prim_assert.sv"

module aes_ctr_fsm import aes_pkg::*;
(
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     incr_i,     // Sparsify using multi-rail.
  output logic                     ready_o,    // Sparsify using multi-rail.
  input  logic                     incr_err_i,
  input  logic                     mr_err_i,
  output logic                     alert_o,

  output logic [SliceIdxWidth-1:0] ctr_slice_idx_o,
  input  logic  [SliceSizeCtr-1:0] ctr_slice_i,
  output logic  [SliceSizeCtr-1:0] ctr_slice_o,
  output logic                     ctr_we_o    // Sparsify using multi-rail.
);

  // Signals
  aes_ctr_e                 aes_ctr_ns, aes_ctr_cs;
  logic [SliceIdxWidth-1:0] ctr_slice_idx_d, ctr_slice_idx_q;
  logic                     ctr_carry_d, ctr_carry_q;

  logic    [SliceSizeCtr:0] ctr_value;

  /////////////
  // Counter //
  /////////////

  // We do SliceSizeCtr bits at a time.
  assign ctr_value   = ctr_slice_i + {{(SliceSizeCtr-1){1'b0}}, ctr_carry_q};
  assign ctr_slice_o = ctr_value[SliceSizeCtr-1:0];

  /////////////
  // Control //
  /////////////

  // FSM
  always_comb begin : aes_ctr_fsm_comb

    // Outputs
    ready_o         = 1'b0;
    ctr_we_o        = 1'b0;
    alert_o         = 1'b0;

    // FSM
    aes_ctr_ns      = aes_ctr_cs;
    ctr_slice_idx_d = ctr_slice_idx_q;
    ctr_carry_d     = ctr_carry_q;

    unique case (aes_ctr_cs)
      CTR_IDLE: begin
        ready_o = 1'b1;
        if (incr_i == 1'b1) begin
          // Initialize slice index and carry bit.
          ctr_slice_idx_d = '0;
          ctr_carry_d     = 1'b1;
          aes_ctr_ns      = CTR_INCR;
        end
      end

      CTR_INCR: begin
        // Increment slice index.
        ctr_slice_idx_d = ctr_slice_idx_q + SliceIdxWidth'(1);
        ctr_carry_d     = ctr_value[SliceSizeCtr];
        ctr_we_o        = 1'b1;

        if (ctr_slice_idx_q == {SliceIdxWidth{1'b1}}) begin
          aes_ctr_ns = CTR_IDLE;
        end
      end

      CTR_ERROR: begin
        // SEC_CM: CTR.FSM.LOCAL_ESC
        // Terminal error state
        alert_o = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious
      // glitch), error out immediately.
      default: begin
        aes_ctr_ns = CTR_ERROR;
        alert_o = 1'b1;
      end
    endcase

    // Unconditionally jump into the terminal error state in case an error is detected.
    if (incr_err_i || mr_err_i) begin
      aes_ctr_ns = CTR_ERROR;
    end
  end

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctr_slice_idx_q <= '0;
      ctr_carry_q     <= '0;
    end else begin
      ctr_slice_idx_q <= ctr_slice_idx_d;
      ctr_carry_q     <= ctr_carry_d;
    end
  end

  // SEC_CM: CTR.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, aes_ctr_ns, aes_ctr_cs, aes_ctr_e, CTR_IDLE)

  // Forward slice index.
  assign ctr_slice_idx_o = ctr_slice_idx_q;

  ////////////////
  // Assertions //
  ////////////////
  `ASSERT(AesCtrStateValid, !alert_o |-> aes_ctr_cs inside {
      CTR_IDLE,
      CTR_INCR
      })

endmodule
