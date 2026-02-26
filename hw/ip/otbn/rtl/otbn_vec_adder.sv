// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * OTBN vectorized adder
 *
 * This module implements a configurable vectorized adder which performs element-wise
 * additions on two input vectors. The element widths of the vectors is dynamically controllable.
 *
 * For the addition, the vector is split into LNVecProc chunks, each LVChunkLEN bits wide. The
 * use_ext_carry_i signal controls the carry chain between the chunk adders:
 * - When 0: The carry output from the previous (less significant) chunk is propagated, chaining
 *   the adders together to form a wider effective element.
 * - When 1: The carry chain is broken, and the adder uses the external carry provided
 *   in carries_in_i. Note: Adder 0 always takes its carry from carries_in_i[0].
 *
 * This carry chaining allows to compute additions over multiples of LVChunkLEN wide elements
 * including the full vector width (i.e., a non vectorized addition). A subtraction can be
 * performed by setting the operand_b_invert_i signal and the input carries to one because:
 * a - b = a + ~b + 1
 *
 * Blanking is not applied on the datapath and must be handled in the module using this adder.
 *
 * The following diagram shows the internal structure for a VChunkLEN of 32-bits and a total vector
 * length of 256 bits. The MUXs for the carry selection are controlled by the use_ext_carry_i
 * signal.
 *
 * A0 = A[31:0], A1 = [63:32], ..., A15 = A[255:224], same for B
 *
 *   {A7,1}   B7        cin[7]          {A1,1}   B1        cin[1]    {A0,1}  B0         cin[0]
 *      |     |            |               |     |            |        |     |            |
 *      |     |  +----+    |               |     |  +----+    |        |     |  +---------+
 *      |     |  |    |    |               |     |  |    |    |        |     |  |
 *      |   +------+  | /|-+               |   +------+  | /|-+        |   +------+
 *      |   |  {}  |  +-||                 |   |  {}  |  +-||          |   |  {}  |
 *      |   +------+  | \|-+               |   +------+  | \|-+        |   +------+
 *      |       |     |    |               |       |     |    |        |       |
 *    +----------------+   |              +----------------+  |       +----------------+
 *  +-|    Adder  7    |   +-  .....    +-|    Adder  1    |  +-----+-|    Adder  0    |
 *  | +----------------+                | +----------------+        | +----------------+
 *  |         |                         |         |                 |         |
 *  |      [32:1]                       |      [32:1]               |      [32:1]
 *  |         |                         |         |                 |         |
 * cout[7]    |                       cout[1]     |               cout[0]     |
 *            |                                   |                           |
 *       sum[255:224]                        sum[63:32]                   sum[31:0]
 */
module otbn_vec_adder
  import otbn_pkg::*;
#(
  // The following parameters are also defined in the otbn_pkg.sv
  // We prefix it with 'L' to differentiate between the local and global parameter to allow
  // different instantiations.

  // The total length of the vectors (usually 256 bits).
  parameter int LVLEN      = VLEN,
  // The vector chunk length. This defines the width of the internal adders.
  parameter int LVChunkLEN = VChunkLEN,
  // The number of vector chunks, i.e., the number of adders.
  localparam int LNVecProc = LVLEN / LVChunkLEN
) (
  input  logic [LVLEN-1:0]     operand_a_i,
  input  logic [LVLEN-1:0]     operand_b_i,
  input  logic                 operand_b_invert_i,
  input  logic [LNVecProc-1:0] carries_in_i,
  // Controls the carry propagation. Set according to the desired ELEN.
  // Can be a predecoded signal for hardening reasons.
  // Adder 0 always takes the external carry independently of the value given here.
  input  logic [LNVecProc-1:0] use_ext_carry_i,
  output logic [LVLEN-1:0]     sum_o,
  output logic [LNVecProc-1:0] carries_out_o
);
  logic [LNVecProc-1:0] adders_carry_out;

  for (genvar i_adder = 0; i_adder < LNVecProc; i_adder++) begin : g_adders
    logic [LVChunkLEN-1:0] op_a;
    logic [LVChunkLEN:0]   adder_op_a;
    logic [LVChunkLEN-1:0] op_b;
    logic [LVChunkLEN:0]   adder_op_b;
    logic                  prev_carry_out;
    logic                  carry_in;
    logic [LVChunkLEN+1:0] result;

    // Select the carry in depending on the ELEN. Take previous stage or external carry.
    // Adder 0 always takes the external carry.
    assign prev_carry_out = i_adder == 0 ? carries_in_i[0] : adders_carry_out[i_adder - 1];
    assign carry_in = use_ext_carry_i[i_adder] ? carries_in_i[i_adder] : prev_carry_out;

    // Extract and preprocess the operands
    assign op_a = operand_a_i[i_adder * LVChunkLEN+:LVChunkLEN];
    assign op_b = operand_b_invert_i ? ~operand_b_i[i_adder * LVChunkLEN+:LVChunkLEN]
                                     :  operand_b_i[i_adder * LVChunkLEN+:LVChunkLEN];

    // Compute op_a + op_b + carry_in using a two-operand addition. By appending 1'b1 and carry_in
    // as the LSBs, the addition of the LSB position (1 + carry_in) generates a carry into the
    // upper bits exactly when carry_in is set, so result[LVChunkLEN:1] = op_a + op_b + carry_in
    // and result[LVChunkLEN+1] is the carry out. The LSB of result is unused.
    assign adder_op_a = {op_a, 1'b1};
    assign adder_op_b = {op_b, carry_in};

    assign result = adder_op_a + adder_op_b;
    assign adders_carry_out[i_adder] = result[LVChunkLEN+1];

    // Assign the result and carries in the same generated block
    // to avoid a verilator UNOPTFLAT warning.
    assign sum_o[i_adder * LVChunkLEN+:LVChunkLEN] = result[LVChunkLEN:1];
    assign carries_out_o[i_adder] = adders_carry_out[i_adder];

    // The LSB is unused
    logic unused_adder_res_lsb;
    assign unused_adder_res_lsb = result[0];
  end

  `ASSERT_INIT(LvlenDivideNoRemainder_A, (LVLEN % LVChunkLEN) == 0)

endmodule
