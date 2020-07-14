// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN execute block for the base instruction subset
 *
 * This ALU supports the execution of all of OTBN's base instruction subset.
 */
module otbn_alu_base
  import otbn_pkg::*;
(
  // Block is combinatorial; clk/rst are for assertions only.
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  alu_base_operation_t  operation_i,

  output logic [31:0]          result_o,
  output logic                 comparison_result_o
);

  always_comb begin
    unique case (operation_i.op)
      AluOpAdd: begin
        result_o = operation_i.operand_a + operation_i.operand_b;
        comparison_result_o = operation_i.operand_a == operation_i.operand_b;
      end
      default: begin
        result_o = '0;
        comparison_result_o = 1'b0;
      end
    endcase
  end
endmodule
