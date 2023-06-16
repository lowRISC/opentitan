// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
  input logic                                clk_i,
  input logic                                rst_ni,
  input logic [EntropyWidth-1:0]             entropy_i,
  input logic [NumChunks-1:0]                prng_seed_en,
  input logic [NumChunks-1:0][ChunkSize-1:0] prng_seed,
  input logic [ChunkSize-1:0]                lfsr_q_0,
  input logic [ChunkSize-1:0]                lfsr_q_1,
  input logic [ChunkSize-1:0]                lfsr_q_2,
  input logic [ChunkSize-1:0]                lfsr_q_3,
  input logic [ChunkSize-1:0]                lfsr_q_4
  );

  // make sure the entropy received from EDN goes into the masking prng_seed signals
  `ASSERT(EdnInputMatchesMaskingPrngSeed0_A, prng_seed_en[0] |-> ##1 entropy_i == prng_seed[0])
  `ASSERT(EdnInputMatchesMaskingPrngSeed1_A, prng_seed_en[1] |-> ##1 entropy_i == prng_seed[1])
  `ASSERT(EdnInputMatchesMaskingPrngSeed2_A, prng_seed_en[2] |-> ##1 entropy_i == prng_seed[2])
  `ASSERT(EdnInputMatchesMaskingPrngSeed3_A, prng_seed_en[3] |-> ##1 entropy_i == prng_seed[3])
  `ASSERT(EdnInputMatchesMaskingPrngSeed4_A, prng_seed_en[4] |-> ##1 entropy_i == prng_seed[4])
  // make sure masking prng_seed signals match the PRNG LSFR inputs
  `ASSERT(MaskingPrngSeedMatchesLfsrInput0_A, prng_seed_en[0] |-> ##1 prng_seed[0] == lfsr_q_0)
  `ASSERT(MaskingPrngSeedMatchesLfsrInput1_A, prng_seed_en[1] |-> ##1 prng_seed[1] == lfsr_q_1)
  `ASSERT(MaskingPrngSeedMatchesLfsrInput2_A, prng_seed_en[2] |-> ##1 prng_seed[2] == lfsr_q_2)
  `ASSERT(MaskingPrngSeedMatchesLfsrInput3_A, prng_seed_en[3] |-> ##1 prng_seed[3] == lfsr_q_3)
  `ASSERT(MaskingPrngSeedMatchesLfsrInput4_A, prng_seed_en[4] |-> ##1 prng_seed[4] == lfsr_q_4)
endinterface // aes_masking_reseed_if
