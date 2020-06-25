// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_alu #(
  parameter int unsigned RegWidth = 256
) (
  input logic clk_i,
  input logic rst_ni,

  input logic [RegWidth-1:0] a_i,
  input logic [RegWidth-1:0] b_i,
  input logic [11:0] imm_i,

  input logic       shift_left_i,
  input logic [7:0] shift_amt_i,

  input logic imm_sel_i,
  input logic sub_en_i,
  input logic shift_en_i,
  input logic psuedo_mod_i,

  input logic [RegWidth-1:0] mod_wr_data_i,
  input logic                mod_wr_en_i,

  output logic [RegWidth-1:0] res_o
);

  logic [RegWidth-1:0] shift_upper;

  logic [RegWidth-1:0] shift_imm_mux;

  logic [RegWidth:0] add_op_a;
  logic [RegWidth:0] add_op_b;
  logic [RegWidth:0] add_res;

  logic [RegWidth-1:0] mod_q;
  logic [RegWidth-1:0] pseudo_mod_result;

  logic [RegWidth-1:0] shift_out;

  assign shift_upper = shift_en_i ? a_i : {RegWidth{1'b0}};

  otbn_shift otbn_shift_i (
    .lower_i      ( b_i          ),
    .upper_i      ( shift_upper  ),
    .shift_left_i ( shift_left_i ),
    .shift_amt_i  ( shift_amt_i  ),
    .res_o        ( shift_out    )
  );

  assign shift_imm_mux = imm_sel_i ? {{(RegWidth-12){1'b0}}, imm_i} : shift_out;
  assign add_op_a = {a_i, 1'b1};
  assign add_op_b = sub_en_i ? {~shift_imm_mux, 1'b1} : {shift_imm_mux, 1'b0};

  assign add_res = add_op_a + add_op_b;

  always @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mod_q <= '0;
    end else if (mod_wr_en_i) begin
      mod_q <= mod_wr_data_i;
    end
  end

  assign pseudo_mod_result = psuedo_mod_i ? add_res[RegWidth:1] - mod_q : add_res[RegWidth:1];
  assign res_o = shift_en_i ? shift_out : pseudo_mod_result;
endmodule
