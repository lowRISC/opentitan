// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Vectorized Modulo Result Selector
 *
 * This module implements the result selection for regular as well as vectorized pseudo-modulo
 * additions and subtractions. It also supports pushing through the adder Y result unchanged. This
 * is useful for regular additions/subtractions as we can save one input to the final result mux
 * (see otbn_alu_bignum.sv).
 *
 * The otbn_alu_bignum calculates pseudo modulo addition and subtraction by using two adders and
 * evaluating their carry bits. Depending on the carry bits adder X or Y is selected as result.
 *
 * For addition, subtract mod if a + b >= mod:
 * - Adder X calculates X = a + b
 * - Adder Y calculates Y = X - mod
 *
 * - If X generates a carry:
 *   a+b > mod (as mod is 256b) -> Select Y as result
 *
 * - If Y generates a carry:
 *   X-mod = (a+b) - mod >= 0 hence a+b >= mod -> Select Y as result
 *   Note this is only valid if X does not generate a carry.
 *
 * - If no carry is generated:
 *   a + b < mod -> Select X as result
 *
 * For subtraction, add mod if a - b < 0:
 * - Adder X calculates X = a - b
 * - Adder Y calculates Y = X + mod
 *
 * - If X generates a carry:
 *   a - b >= 0 -> Select X as result
 *
 * - Otherwise:
 *   a - b < 0 and thus select Y as result
 *
 * For vectorized calculations this selection must be performed for each vector element
 * independently.
 *
 * Internally the selection process is split up into a decision and selection stage.
 *
 * Decision Stage:
 * The decision stages compute the decisions for each vector chunk separately and thus independent
 * of the vector element length. The decision depends on the operation (add or sub) as
 * described above.
 *
 * Selection Stage:
 * The final result is selected based on the decision bits and the configured element length.
 * The element length (256-bit or 32-bit) selects the appropriate decision bit for each result
 * chunk.
 *
 * X0 = X[31:0], X1 = X[63:32], ..., X7 = X[255:224], same for Y
 * Di = Decision by carry bits CXi and CYi
 *
 * D7                           D7   D6                             D7   D0
 *  |                            |   |                               |   |
 *  |                          \-------/                           \-------/
 *  |         Y7   X7   ELEN -->\-----/      Y6   X6   ...  ELEN -->\-----/      Y0   X0
 *  |          |   |               |          |   |                    |          |   |
 *  |        \-------/             |        \-------/                  |        \-------/
 *  +-------->\-1-0-/              +-------->\-1-0-/                   +-------->\-1-0-/
 *   select_y[7] |                  select_y[6] |                       select_y[0] |
 *               |                              |                                   |
 *         res[255:224]                   res[223:192]                         res[31:0]
 *
 * This stage generates an additional signal whether any vector element uses the result of adder Y.
 * For modulo-addition the Y result is always used. Either as condition to evaluate the MOD test or
 * as actual result. For the push through it is obviously used.
 */
module otbn_mod_result_selector
  import otbn_pkg::*;
(
  input  logic [VLEN-1:0]     result_x_i,
  input  logic [NVecProc-1:0] carries_x_i,
  input  logic [VLEN-1:0]     result_y_i,
  input  logic [NVecProc-1:0] carries_y_i,
  input  logic                is_subtraction_i,
  input  logic                is_modulo_i,
  input  alu_elen_e           elen_i,
  output logic [VLEN-1:0]     result_o,
  output logic                adder_y_used_o
);
  ////////////////////
  // Decision stage //
  ////////////////////
  // Compute for each vector chunk whether to take the result of adder X or Y based upon the
  // carries. See explanation in header. For non-modulo instructions we always decide for the Y
  // result to push it through this selection logic unchanged.
  logic [NVecProc-1:0] decided_for_y;
  assign decided_for_y = !is_modulo_i     ? '1                        :
                         is_subtraction_i ? ~carries_x_i              :
                                            carries_x_i | carries_y_i;

  /////////////////////
  // Selection stage //
  /////////////////////
  // Choose the decision bits based upon the vector element length.
  logic [NVecProc-1:0] select_y;
  always_comb begin
    unique case (elen_i)
      AluElen32:  select_y = decided_for_y;
      AluElen256: select_y = {NVecProc{decided_for_y[NVecProc-1]}};
      default:    select_y = decided_for_y;
    endcase
  end

  // Select X or Y for each chunk based upon the selection logic.
  for (genvar i_res = 0; i_res < NVecProc; i_res++) begin : g_assign_results
    assign result_o[i_res * VChunkLEN+:VChunkLEN] =
        select_y[i_res] ? result_y_i[i_res * VChunkLEN+:VChunkLEN]
                        : result_x_i[i_res * VChunkLEN+:VChunkLEN];
  end

  // Signal whether the result of Y is used or evaluated for any of the chunks. The adder Y result
  // is always used for a push through (non modulo operation). For modulo subtractions the Y result
  // is used if at least one chunk requires the Y. For addition the Y result is always used because
  // we evaluate its carry bits for the decision.
  assign adder_y_used_o = !is_modulo_i     ? 1'b1      :
                          is_subtraction_i ? |select_y : 1'b1;

endmodule
