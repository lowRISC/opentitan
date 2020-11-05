// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A formal testbench for the ICache. This gets bound into the actual ICache DUT.

`include "prim_assert.sv"

module formal_tb (
   // Top-level ports
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             mult_en_i,  // dynamic enable signal, for FSM control
    input  logic             div_en_i,   // dynamic enable signal, for FSM control
    input  logic             mult_sel_i, // static decoder input, for data muxes
    input  logic             div_sel_i,  // static decoder input, for data muxes
    input  ibex_pkg::md_op_e operator_i,
    input  logic       [1:0] signed_mode_i,
    input  logic      [31:0] op_a_i,
    input  logic      [31:0] op_b_i,
    input  logic      [33:0] alu_adder_ext_i,
    input  logic      [31:0] alu_adder_i,
    input  logic             equal_to_zero_i,
    input  logic             data_ind_timing_i,

    input logic      [32:0]  alu_operand_a_o,
    input logic      [32:0]  alu_operand_b_o,

    input logic      [33:0]  imd_val_q_i[1:0],
    input logic      [33:0]  imd_val_d_o[1:0],
    input logic       [1:0]  imd_val_we_o,

    input  logic             multdiv_ready_id_i,

    input logic      [31:0]  multdiv_result_o,

    input logic              valid_o
);

  import ibex_pkg::*;

  logic [2:0] f_startup_count = 3'd0;
  always_ff @(posedge clk_i) begin : reset_assertion
    f_startup_count <= f_startup_count + ((f_startup_count == 3'd5) ? 3'd0 : 3'd1);
    // Assume that rst_ni is low for the first cycle and not true after that.
    assume (~((f_startup_count == 3'd0) ^ ~rst_ni));
  end

  `include "multdiv_operation.svh"
  // Defines with DATA_IND_OP_COUNT the number of cycles the current check must have.
  `include "multdiv_check.svh"

  logic [5:0] f_operation_count = 6'd0;

  logic checked = 1'b0;

  always_ff @(posedge clk_i) begin : count_assertion
    if (f_startup_count >= 3'd1) begin
      f_operation_count <= f_operation_count + 1;
    end
  end

  always_ff @(posedge clk_i) begin : check
    if (!checked && (valid_o || (f_operation_count == DATA_IND_OP_COUNT))) begin
      checked <= 1'b1;
      assert (valid_o && (f_operation_count == DATA_IND_OP_COUNT));
      assume (multdiv_ready_id_i);
    end
  end

  always_comb begin
    if (f_operation_count > DATA_IND_OP_COUNT) begin
      assert (checked);
    end
  end

endmodule
