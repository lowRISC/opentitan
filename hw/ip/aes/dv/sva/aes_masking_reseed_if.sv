// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface for verifying the reseed activity of the masking PRNG inside AES. This interface
// can only be used if masking is enabled via compile-time parameter. If masking is disabled,
// only the aes_reseed_if interface can be used.

`include "prim_assert.sv"

interface aes_masking_reseed_if
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH,
  parameter int unsigned StateWidth   = prim_trivium_pkg::BiviumStateWidth
) (
  input logic clk_i,
  input logic rst_ni,

  // Entropy request/ack signals
  input logic entropy_masking_req,
  input logic entropy_masking_ack,

  // Entropy input and PRNG state signals
  input logic [EntropyWidth-1:0] entropy_i,
  input logic [StateWidth-1:0]   state_q,

  // Control signals
  input logic      block_ctr_expr,
  input aes_ctrl_e ctrl_state,
  input aes_ctrl_e ctrl_state_next,
  input logic      alert_fatal
);

  localparam int unsigned LastStatePartFractional = StateWidth % EntropyWidth != 0 ? 1 : 0;
  localparam int unsigned NumStateParts = StateWidth / EntropyWidth + LastStatePartFractional;
  localparam int unsigned NumBitsLastPart = StateWidth - (NumStateParts - 1) * EntropyWidth;
  localparam int unsigned LastStatePart = NumStateParts - 1;

  logic [NumStateParts-1:0] state_part_matches_input;
  always_comb begin
    state_part_matches_input = '0;
    for (int unsigned i = 0; i < LastStatePart; i++) begin
      state_part_matches_input[i] = state_q[i * EntropyWidth +: EntropyWidth] == entropy_i;
    end
    state_part_matches_input[LastStatePart] =
        state_q[StateWidth - 1 -: NumBitsLastPart] == entropy_i[NumBitsLastPart-1:0];
  end

  // Make sure the entropy input obtained from EDN actually ends up in one part of the PRNG state.
  `ASSERT(MaskingPrngStatePartMatchesEdnInput_A, entropy_masking_req && entropy_masking_ack
      |-> ##1 |state_part_matches_input)

  // Make sure the masking PRNG is reseeded when a new block is started while the block counter
  // has expired unless a fatal alert is triggered.
  `ASSERT(MaskingPrngReseedWhenCtrExpires_A,
      (block_ctr_expr && (ctrl_state == CTRL_IDLE) && (ctrl_state_next == CTRL_LOAD)) |->
      ##[1:20] entropy_masking_req || alert_fatal)

endinterface // aes_masking_reseed_if
