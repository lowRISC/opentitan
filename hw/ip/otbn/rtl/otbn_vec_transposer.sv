// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Vectorized Transposer
 *
 * This module transposes the elements of two input vectors in two different ways.
 * It supports 32b, 64b and 128b element lengths.
 *
 * The mode trn1 interleaves even coordinates and trn2 odd coordinates.
 * For example, if there are two vectors with 4 elements the results are as follows:
 *
 * Transposition            TRN1                          TRN2
 *                 +----+----+----+----+         +----+----+----+----+
 * Input A         | A3 | A2 | A1 | A0 |         | A3 | A2 | A1 | A0 |
 *                 +----+----+----+----+         +----+----+----+----+
 *                 +----+----+----+----+         +----+----+----+----+
 * Input B         | B3 | B2 | B1 | B0 |         | B3 | B2 | B1 | B0 |
 *                 +----+----+----+----+         +----+----+----+----+
 *                 +----+----+----+----+         +----+----+----+----+
 * Result          | B2 | A2 | B0 | A0 |         | B3 | A3 | B1 | A1 |
 *                 +----+----+----+----+         +----+----+----+----+
 */
module otbn_vec_transposer
  import otbn_pkg::*;
(
  // For assertions only.
  input logic clk_i,
  input logic rst_ni,

  input  logic [VLEN-1:0] operand_a_i,
  input  logic [VLEN-1:0] operand_b_i,
  input  logic            is_trn1_i,
  input  trn_elen_e       elen_i,
  output logic [VLEN-1:0] result_o
);

  typedef struct packed {
    logic [31:0] chunk;
  } vector_chunk_t;

  logic [VLEN-1:0] res_trn1;
  logic [VLEN-1:0] res_trn2;

  vector_chunk_t [7:0] vec_a;
  vector_chunk_t [7:0] vec_b;

  assign vec_a = operand_a_i;
  assign vec_b = operand_b_i;

  always_comb begin
    unique case (elen_i)
      TrnElen32: begin
        res_trn1 = {vec_b[6], vec_a[6], vec_b[4], vec_a[4],
                    vec_b[2], vec_a[2], vec_b[0], vec_a[0]};
        res_trn2 = {vec_b[7], vec_a[7], vec_b[5], vec_a[5],
                    vec_b[3], vec_a[3], vec_b[1], vec_a[1]};
      end
      TrnElen64: begin
        res_trn1 = {vec_b[5], vec_b[4], vec_a[5], vec_a[4],
                    vec_b[1], vec_b[0], vec_a[1], vec_a[0]};
        res_trn2 = {vec_b[7], vec_b[6], vec_a[7], vec_a[6],
                    vec_b[3], vec_b[2], vec_a[3], vec_a[2]};
      end
      TrnElen128: begin
        res_trn1 = {vec_b[3], vec_b[2], vec_b[1], vec_b[0],
                    vec_a[3], vec_a[2], vec_a[1], vec_a[0]};
        res_trn2 = {vec_b[7], vec_b[6], vec_b[5], vec_b[4],
                    vec_a[7], vec_a[6], vec_a[5], vec_a[4]};
      end
      default: begin // Default is 32-bit case
        res_trn1 = {vec_b[6], vec_a[6], vec_b[4], vec_a[4],
                    vec_b[2], vec_a[2], vec_b[0], vec_a[0]};
        res_trn2 = {vec_b[7], vec_a[7], vec_b[5], vec_a[5],
                    vec_b[3], vec_a[3], vec_b[1], vec_a[1]};
      end
    endcase
  end

  assign result_o = is_trn1_i ? res_trn1 : res_trn2;

  // clk_i and rst_ni are only used by assertions
  logic unused_clk;
  logic unused_rst_n;

  assign unused_clk   = clk_i;
  assign unused_rst_n = rst_ni;

  // Assert VLEN = 256 as otherwise this module does not work properly.
  `ASSERT_INIT(OtbnVecTransposerUnsupportedVLEN, VLEN == 256)

  `ASSERT(OtbnVecTransposerInvalidElen, elen_i inside {TrnElen32, TrnElen64, TrnElen128})
endmodule
