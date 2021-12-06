// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES counter FSM for CTR mode
//
// This module contains the AES counter FSM operating on and producing the negated values of
// important control signals. This is achieved by:
// - instantiating the regular AES counter FSM operating on and producing the positive values of
//   these signals, and
// - inverting these signals between the regular FSM and the prim_buf synthesis barriers.
// Synthesis tools will then push the inverters into the actual FSM.

module aes_ctr_fsm_n import aes_pkg::*;
(
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     incr_ni,         // Sparsify using multi-rail.
  output logic                     ready_no,        // Sparsify using multi-rail.
  input  logic                     incr_err_i,
  input  logic                     mr_err_i,
  output logic                     alert_o,

  output logic [SliceIdxWidth-1:0] ctr_slice_idx_o,
  input  logic  [SliceSizeCtr-1:0] ctr_slice_i,
  output logic  [SliceSizeCtr-1:0] ctr_slice_o,
  output logic                     ctr_we_no        // Sparsify using multi-rail.
);

  /////////////////////
  // Input Buffering //
  /////////////////////

  localparam int NumInBufBits = $bits({
    incr_ni,
    incr_err_i,
    mr_err_i,
    ctr_slice_i
  });

  logic [NumInBufBits-1:0] in, in_buf;

  assign in = {
    incr_ni,
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

  logic                    incr_n;
  logic                    incr_err;
  logic                    mr_err;
  logic [SliceSizeCtr-1:0] ctr_i_slice;

  assign {incr_n,
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

  // The regular FSM operates on and produces the positive values of important control signals.
  // Invert *_n input signals here to get the positive values for the regular FSM. To obtain the
  // negated outputs, important output signals are inverted further below. Thanks to the prim_buf
  // synthesis optimization barriers, tools will push the inverters into the regular FSM.
  aes_ctr_fsm u_aes_ctr_fsm (
    .clk_i           ( clk_i         ),
    .rst_ni          ( rst_ni        ),

    .incr_i          ( ~incr_n       ), // Invert for regular FSM.
    .ready_o         ( ready         ), // Invert below for negated output.
    .incr_err_i      ( incr_err      ),
    .mr_err_i        ( mr_err        ),
    .alert_o         ( alert         ),

    .ctr_slice_idx_o ( ctr_slice_idx ),
    .ctr_slice_i     ( ctr_i_slice   ),
    .ctr_slice_o     ( ctr_o_slice   ),
    .ctr_we_o        ( ctr_we        )  // Invert below for negated output.
  );

  //////////////////////
  // Output Buffering //
  //////////////////////

  localparam int NumOutBufBits = $bits({
    ready_no,
    alert_o,
    ctr_slice_idx_o,
    ctr_slice_o,
    ctr_we_no
  });

  logic [NumOutBufBits-1:0] out, out_buf;

  // Important output control signals need to be inverted here. Synthesis tools will push the
  // inverters back into the regular FSM.
  assign out = {
    ~ready,
    alert,
    ctr_slice_idx,
    ctr_o_slice,
    ~ctr_we
  };

  // This primitive is used to place a size-only constraint on the
  // buffers to act as a synthesis optimization barrier.
  prim_buf #(
    .Width(NumOutBufBits)
  ) u_prim_buf_out (
    .in_i(out),
    .out_o(out_buf)
  );

  assign {ready_no,
          alert_o,
          ctr_slice_idx_o,
          ctr_slice_o,
          ctr_we_no} = out_buf;

endmodule
