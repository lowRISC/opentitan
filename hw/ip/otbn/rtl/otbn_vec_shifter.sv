// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * OTBN vectorized shifter
 *
 * This shifter can perform logical shifts on vectors elementwise as well as concatenate and shift
 * 256 bit registers. The shifter takes a 512-bit input (to implement BN.RSHI, concatenate and
 * right shift) and shifts right by up to 256-bits. The lower (256-bit) half of the input and
 * output can be reversed to enable a left shift operation. There is no concatenate and left shift
 * instruction so reversing isn't required over the full width. If there is no concatenation, the
 * upper input must be all-zero.
 *
 * Shifting vectors elementwise is enabled by adding a masking step after the shifting.
 * For this an element width dependent mask must be provided which then will clear the bits
 * overflowing into the neighboring element.
 *
 * Example:
 * Assume there is a vector with 2 4-bit elements:
 *   |0101 1010|
 *
 * This should be shifted >> by 2. The expected result is:
 *   |0001 0010|
 *
 * The regular shifting process would give:
 *   |0001 0110|
 *
 * so the lower 2 bits of the upper element are shifted into the lower element. To correct this,
 * the mask 8'b00110011 must be provided. This mask is then applied and clears the overflowing
 * bits.
 *
 *    |0001 0110|
 *  & |0011 0011|
 *  = |0001 0010|
 *
 * This approach natively supports 256-bit elements by setting the mask to all-ones.
 *
 * in_upper    in_lower
 *    |           |
 *    |       +---+---+
 *    |       |       |
 *    |       |    +-----+
 *    |       |    | rev |  reverse the input
 *    |       |    +-----+
 *    |       |       |
 *    |       |   +---+
 *    |       |   |
 *    |     \-------/ <-- shift_direction
 *    |         |
 *    |   +-----+
 *    |   |
 *  +-------+
 *  |  >>   | <-- shift_amount
 *  +-------+
 *      |
 * +---------+
 * | [255:0] |
 * +---------+
 *      |
 * +---------+
 * | mask &  | <-- vector_mask
 * +---------+
 *   |     |
 *   |     |
 *   |  +-----+
 *   |  | rev | reverse the input back
 *   |  +-----+
 *   |     |
 *   |   +-+
 *   |   |
 * \-------/ <-- shift_direction
 *     |
 * shift_result
 *
 */
module otbn_vec_shifter
  import otbn_pkg::*;
(
  // Clock and reset only for assertions in onehot MUXs
  input  logic clk_i,
  input  logic rst_ni,

  input  logic [WLEN-1:0]         shifter_in_upper_i,
  input  logic [WLEN-1:0]         shifter_in_lower_i,
  input  logic [1:0]              shift_direction_i,
  input  logic [$clog2(WLEN)-1:0] shift_amt_i,
  input  logic [WLEN-1:0]         vector_mask_i,
  output logic [WLEN-1:0]         shifter_res_o
);
  logic [WLEN*2-1:0] shifter_in;
  logic [WLEN*2-1:0] shifter_out;
  logic [WLEN-1:0]   shifter_in_lower_mux [2];
  logic [WLEN-1:0]   shifter_in_lower_reverse;
  logic [WLEN-1:0]   shifter_in_lower;
  logic [WLEN-1:0]   shifter_out_lower_mux [2];
  logic [WLEN-1:0]   shifter_out_lower;
  logic [WLEN-1:0]   shifter_out_lower_reverse;
  logic [WLEN-1:0]   shifter_masked;

  for (genvar i = 0; i < WLEN; i++) begin : g_shifter_in_lower_reverse
    assign shifter_in_lower_reverse[i] = shifter_in_lower_i[WLEN-i-1];
  end

  assign shifter_in_lower_mux[AluShiftDirLeft]  = shifter_in_lower_reverse;
  assign shifter_in_lower_mux[AluShiftDirRight] = shifter_in_lower_i;

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width (WLEN),
    .Inputs(2)
  ) u_lower_input_mux (
    .clk_i,
    .rst_ni,
    .in_i  (shifter_in_lower_mux),
    .sel_i (shift_direction_i),
    .out_o (shifter_in_lower)
  );

  assign shifter_in = {shifter_in_upper_i, shifter_in_lower};

  assign shifter_out = shifter_in >> shift_amt_i;

  // Mask out overflowing bits of the adjacent vector elements
  assign shifter_masked = shifter_out[WLEN-1:0] & vector_mask_i;

  assign shifter_out_lower = shifter_masked;

  for (genvar i = 0; i < WLEN; i++) begin : g_shifter_out_lower_reverse
    assign shifter_out_lower_reverse[i] = shifter_out_lower[WLEN-i-1];
  end

  assign shifter_out_lower_mux[AluShiftDirLeft]  = shifter_out_lower_reverse;
  assign shifter_out_lower_mux[AluShiftDirRight] = shifter_out_lower;

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width (WLEN),
    .Inputs(2)
  ) u_out_mux (
    .clk_i,
    .rst_ni,
    .in_i  (shifter_out_lower_mux),
    .sel_i (shift_direction_i),
    .out_o (shifter_res_o)
  );

  // Only the lower WLEN bits of the shift result are returned.
  logic unused_shifter_out_upper;
  assign unused_shifter_out_upper = ^shifter_out[WLEN*2-1:WLEN];
endmodule
