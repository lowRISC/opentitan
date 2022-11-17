// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES counter for CTR mode
//
// This module uses one counter with a width of SliceSizeCtr to iteratively increment the 128-bit
// counter value.

module aes_ctr import aes_pkg::*;
(
  input  logic                                       clk_i,
  input  logic                                       rst_ni,

  input  sp2v_e                                      incr_i,
  output sp2v_e                                      ready_o,
  output logic                                       alert_o,

  input  logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] ctr_i,
  output logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] ctr_o,
  output sp2v_e [NumSlicesCtr-1:0]                   ctr_we_o
);

  // Reverse byte order - unrelated to NumSlicesCtr and SliceSizeCtr
  function automatic logic [15:0][7:0] aes_rev_order_byte(logic [15:0][7:0] in);
    logic [15:0][7:0] out;
    for (int i = 0; i < 16; i++) begin
      out[i] = in[15-i];
    end
    return out;
  endfunction

  // Reverse sp2v order
  function automatic sp2v_e [NumSlicesCtr-1:0] aes_rev_order_sp2v(sp2v_e [NumSlicesCtr-1:0] in);
    sp2v_e [NumSlicesCtr-1:0] out;
    for (int i = 0; i < NumSlicesCtr; i++) begin
      out[i] = in[NumSlicesCtr - 1 - i];
    end
    return out;
  endfunction

  // Signals
  logic                   [SliceIdxWidth-1:0] ctr_slice_idx;

  logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] ctr_i_rev; // 8 times 2 bytes
  logic  [NumSlicesCtr-1:0][SliceSizeCtr-1:0] ctr_o_rev; // 8 times 2 bytes
  sp2v_e [NumSlicesCtr-1:0]                   ctr_we_o_rev;
  sp2v_e                                      ctr_we;

  logic                    [SliceSizeCtr-1:0] ctr_i_slice;
  logic                    [SliceSizeCtr-1:0] ctr_o_slice;

  sp2v_e                                      incr;
  logic                                       incr_err;
  logic                                       mr_err;

  // Sparsified FSM signals. These are needed for connecting the individual bits of the Sp2V
  // signals to the single-rail FSMs.
  logic    [Sp2VWidth-1:0]                    sp_incr;
  logic    [Sp2VWidth-1:0]                    sp_ready;
  logic    [Sp2VWidth-1:0]                    sp_ctr_we;

  // Multi-rail signals. These are outputs of the single-rail FSMs and need combining.
  logic    [Sp2VWidth-1:0]                    mr_alert;
  logic    [Sp2VWidth-1:0][SliceIdxWidth-1:0] mr_ctr_slice_idx;
  logic    [Sp2VWidth-1:0] [SliceSizeCtr-1:0] mr_ctr_o_slice;

  ////////////
  // Inputs //
  ////////////

  // Reverse byte order
  assign ctr_i_rev = aes_rev_order_byte(ctr_i);

  // SEC_CM: CTRL.SPARSE
  // Check sparsely encoded incr signal.
  logic [Sp2VWidth-1:0] incr_raw;
  aes_sel_buf_chk #(
    .Num      ( Sp2VNum   ),
    .Width    ( Sp2VWidth ),
    .EnSecBuf ( 1'b0      )
  ) u_aes_sb_en_buf_chk (
    .clk_i  ( clk_i    ),
    .rst_ni ( rst_ni   ),
    .sel_i  ( incr_i   ),
    .sel_o  ( incr_raw ),
    .err_o  ( incr_err )
  );
  assign incr = sp2v_e'(incr_raw);

  /////////////
  // Counter //
  /////////////

  // We do SliceSizeCtr bits at a time.
  assign ctr_i_slice = ctr_i_rev[ctr_slice_idx];

  /////////
  // FSM //
  /////////

  // Convert sp2v_e signals to sparsified inputs.
  assign sp_incr = {incr};

  // SEC_CM: CTR.FSM.REDUN
  // For every bit in the Sp2V signals, one separate rail is instantiated. The inputs and outputs
  // of every rail are buffered to prevent aggressive synthesis optimizations.
  for (genvar i = 0; i < Sp2VWidth; i++) begin : gen_fsm
    if (SP2V_LOGIC_HIGH[i] == 1'b1) begin : gen_fsm_p
      aes_ctr_fsm_p u_aes_ctr_fsm_i (
        .clk_i           ( clk_i               ),
        .rst_ni          ( rst_ni              ),

        .incr_i          ( sp_incr[i]          ), // Sparsified
        .ready_o         ( sp_ready[i]         ), // Sparsified
        .incr_err_i      ( incr_err            ),
        .mr_err_i        ( mr_err              ),
        .alert_o         ( mr_alert[i]         ), // OR-combine

        .ctr_slice_idx_o ( mr_ctr_slice_idx[i] ), // OR-combine
        .ctr_slice_i     ( ctr_i_slice         ),
        .ctr_slice_o     ( mr_ctr_o_slice[i]   ), // OR-combine
        .ctr_we_o        ( sp_ctr_we[i]        )  // Sparsified
      );
    end else begin : gen_fsm_n
      aes_ctr_fsm_n u_aes_ctr_fsm_i (
        .clk_i           ( clk_i               ),
        .rst_ni          ( rst_ni              ),

        .incr_ni         ( sp_incr[i]          ), // Sparsified
        .ready_no        ( sp_ready[i]         ), // Sparsified
        .incr_err_i      ( incr_err            ),
        .mr_err_i        ( mr_err              ),
        .alert_o         ( mr_alert[i]         ), // OR-combine

        .ctr_slice_idx_o ( mr_ctr_slice_idx[i] ), // OR-combine
        .ctr_slice_i     ( ctr_i_slice         ),
        .ctr_slice_o     ( mr_ctr_o_slice[i]   ), // OR-combine
        .ctr_we_no       ( sp_ctr_we[i]        )  // Sparsified
      );
    end
  end

  // Convert sparsified outputs to sp2v_e type.
  assign ready_o = sp2v_e'(sp_ready);
  assign ctr_we  = sp2v_e'(sp_ctr_we);

  // Combine single-bit FSM outputs.
  // OR: One bit is sufficient to drive the corresponding output bit high.
  assign alert_o = |mr_alert;

  // Combine multi-bit FSM outputs. We simply OR them together and compare the values
  // to detect errors.
  always_comb begin : combine_sparse_signals
    ctr_slice_idx = '0;
    ctr_o_slice   = '0;
    mr_err        = 1'b0;

    for (int i = 0; i < Sp2VWidth; i++) begin
      ctr_slice_idx |= mr_ctr_slice_idx[i];
      ctr_o_slice   |= mr_ctr_o_slice[i];
    end

    for (int i = 0; i < Sp2VWidth; i++) begin
      if (ctr_slice_idx != mr_ctr_slice_idx[i] ||
          ctr_o_slice   != mr_ctr_o_slice[i]) begin
        mr_err = 1'b1;
      end
    end
  end

  /////////////
  // Outputs //
  /////////////

  // Combine input and counter output.
  always_comb begin
    ctr_o_rev                = ctr_i_rev;
    ctr_o_rev[ctr_slice_idx] = ctr_o_slice;
  end

  // Generate the sliced write enable.
  always_comb begin
    ctr_we_o_rev                = {NumSlicesCtr{SP2V_LOW}};
    ctr_we_o_rev[ctr_slice_idx] = ctr_we;
  end

  // Reverse byte and bit order.
  assign ctr_o    = aes_rev_order_byte(ctr_o_rev);
  assign ctr_we_o = aes_rev_order_sp2v(ctr_we_o_rev);

endmodule
