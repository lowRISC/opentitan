// Copyright lowRISC contributors.
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
  parameter int unsigned  EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH,
  parameter int unsigned  Width        = WidthPRDMasking, // Must be divisble by ChunkSize and 8
  parameter int unsigned  ChunkSize    = ChunkSizePRDMasking, // Width of the LFSR primitives
  localparam int unsigned NumChunks    = Width/ChunkSize      // derived parameter
) (
  input logic clk_i,
  input logic rst_ni,

  // Entropy request signal
  input logic entropy_masking_req,

  // Entropy input and LFSR state signals
  input logic [EntropyWidth-1:0] entropy_i,
  input logic [ChunkSize-1:0]    lfsr_q_0,
  input logic [ChunkSize-1:0]    lfsr_q_1,
  input logic [ChunkSize-1:0]    lfsr_q_2,
  input logic [ChunkSize-1:0]    lfsr_q_3,
  input logic [ChunkSize-1:0]    lfsr_q_4,

  // Control signals
  input prs_rate_e            reseed_rate,
  input logic                 block_ctr_expr,
  input aes_ctrl_e            ctrl_state,
  input aes_ctrl_e            ctrl_state_next,
  input logic                 alert_fatal,
  input logic [NumChunks-1:0] seed_en
);

  // Make sure the LFSRs of the masking PRNG are set to the correct values obtained from EDN.
  `ASSERT(MaskingPrngState0MatchesEdnInput_A, seed_en[0] |-> ##1 entropy_i == lfsr_q_0)
  `ASSERT(MaskingPrngState1MatchesEdnInput_A, seed_en[1] |-> ##1 entropy_i == lfsr_q_1)
  `ASSERT(MaskingPrngState2MatchesEdnInput_A, seed_en[2] |-> ##1 entropy_i == lfsr_q_2)
  `ASSERT(MaskingPrngState3MatchesEdnInput_A, seed_en[3] |-> ##1 entropy_i == lfsr_q_3)
  `ASSERT(MaskingPrngState4MatchesEdnInput_A, seed_en[4] |-> ##1 entropy_i == lfsr_q_4)

  // Make sure the masking PRNG is reseeded when a new block is started while the block counter
  // has expired unless a fatal alert is triggered.
  `ASSERT(MaskingPrngReseedWhenCtrExpires_A,
      (block_ctr_expr && (ctrl_state == CTRL_IDLE) && (ctrl_state_next == CTRL_LOAD)) |->
      ##[1:20] entropy_masking_req || alert_fatal)

endinterface // aes_masking_reseed_if
