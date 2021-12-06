// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES counter FSM for CTR mode
//
// This module contains the AES counter FSM operating on and producing the positive values of
// important control signals.

module aes_ctr_fsm_p import aes_pkg::*;
(
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     incr_i,          // Sparsify
  output logic                     ready_o,         // Sparsify
  input  logic                     incr_err_i,
  input  logic                     mr_err_i,
  output logic                     alert_o,

  output logic [SliceIdxWidth-1:0] ctr_slice_idx_o,
  input  logic  [SliceSizeCtr-1:0] ctr_slice_i,
  output logic  [SliceSizeCtr-1:0] ctr_slice_o,
  output logic                     ctr_we_o         // Sparsify
);

  /////////////////////
  // Input Buffering //
  /////////////////////

  localparam int NumInBufBits = $bits({
    incr_i,
    incr_err_i,
    mr_err_i,
    ctr_slice_i
  });

  logic [NumInBufBits-1:0] in, in_buf;

  assign in = {
    incr_i,
    incr_err_i,
    mr_err_i,
    ctr_slice_i
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumInBufBits)
  ) u_prim_buf_in (
    .in_i(in),
    .out_o(in_buf)
  );

  logic                    incr;
  logic                    incr_err;
  logic                    mr_err;
  logic [SliceSizeCtr-1:0] ctr_i_slice;

  assign {incr,
          incr_err,
          mr_err,
          ctr_i_slice} = in_buf;

  // Intermediate output signals
  logic                     ready;
  logic                     alert;
  logic [SliceIdxWidth-1:0] ctr_slice_idx;
  logic  [SliceSizeCtr-1:0] ctr_o_slice;
  logic                     ctr_we;

  /////////////////
  // Regular FSM //
  /////////////////

  aes_ctr_fsm u_aes_ctr_fsm (
    .clk_i           ( clk_i         ),
    .rst_ni          ( rst_ni        ),

    .incr_i          ( incr          ),
    .ready_o         ( ready         ),
    .incr_err_i      ( incr_err      ),
    .mr_err_i        ( mr_err        ),
    .alert_o         ( alert         ),

    .ctr_slice_idx_o ( ctr_slice_idx ),
    .ctr_slice_i     ( ctr_i_slice   ),
    .ctr_slice_o     ( ctr_o_slice   ),
    .ctr_we_o        ( ctr_we        )
  );

  //////////////////////
  // Output Buffering //
  //////////////////////

  localparam int NumOutBufBits = $bits({
    ready_o,
    alert_o,
    ctr_slice_idx_o,
    ctr_slice_o,
    ctr_we_o
  });

  logic [NumOutBufBits-1:0] out, out_buf;

  assign out = {
    ready,
    alert,
    ctr_slice_idx,
    ctr_o_slice,
    ctr_we
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumOutBufBits)
  ) u_prim_buf_out (
    .in_i(out),
    .out_o(out_buf)
  );

  assign {ready_o,
          alert_o,
          ctr_slice_idx_o,
          ctr_slice_o,
          ctr_we_o} = out_buf;

endmodule
