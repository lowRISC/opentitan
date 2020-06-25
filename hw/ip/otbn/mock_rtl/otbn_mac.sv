// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_mac#(
  parameter int unsigned RegWidth = 256
) (
  input logic clk_i,
  input logic rst_ni,

  input logic [RegWidth-1:0] a_i,
  input logic [RegWidth-1:0] b_i,

  input logic [1:0] a_qw_sel_i,
  input logic [1:0] b_qw_sel_i,

  input logic [1:0] pre_acc_shift_i,

  input logic zero_acc_i,

  input logic mac_en_i,
  input logic mul_en_i,

  input logic acc_shift_out_i,

  output logic [RegWidth-1:0] res_o
);

  localparam int unsigned QWWidth = RegWidth / 4;

  logic [RegWidth-1:0] adder_op_a;
  logic [RegWidth-1:0] adder_op_b;
  logic [RegWidth-1:0] adder_res;

  logic [RegWidth/4-1:0] mul_op_a;
  logic [RegWidth/4-1:0] mul_op_b;
  logic [RegWidth/2-1:0] mul_res;
  logic [RegWidth-1:0]   mul_res_shifted;

  logic [RegWidth-1:0] acc;
  logic [RegWidth-1:0] acc_d;
  logic [RegWidth-1:0] acc_q;

  always_comb begin
    mul_op_a = '0;
    mul_op_b = '0;

    unique case(a_qw_sel_i)
      2'd0: mul_op_a = a_i[QWWidth*0+:QWWidth];
      2'd1: mul_op_a = a_i[QWWidth*1+:QWWidth];
      2'd2: mul_op_a = a_i[QWWidth*2+:QWWidth];
      2'd3: mul_op_a = a_i[QWWidth*3+:QWWidth];
      default: mul_op_a = '0;
    endcase

    unique case(b_qw_sel_i)
      2'd0: mul_op_b = b_i[QWWidth*0+:QWWidth];
      2'd1: mul_op_b = b_i[QWWidth*1+:QWWidth];
      2'd2: mul_op_b = b_i[QWWidth*2+:QWWidth];
      2'd3: mul_op_b = b_i[QWWidth*3+:QWWidth];
      default: mul_op_b = '0;
    endcase
  end

  assign mul_res = mul_op_a * mul_op_b;

  always_comb begin
    mul_res_shifted = '0;

    unique case(pre_acc_shift_i)
      2'd0: mul_res_shifted = {{QWWidth*2{1'b0}}, mul_res};
      2'd1: mul_res_shifted = {{QWWidth{1'b0}}, mul_res, {QWWidth{1'b0}}};
      2'd2: mul_res_shifted = {mul_res, {QWWidth*2{1'b0}}};
      2'd3: mul_res_shifted = {mul_res[63:0], {QWWidth*3{1'b0}}};
      default: mul_res_shifted = '0;
    endcase
  end

  assign acc = zero_acc_i ? '0 : acc_q;

  assign adder_op_a = mul_res_shifted;
  assign adder_op_b = acc;

  assign adder_res = adder_op_a + adder_op_b;

  assign acc_d = acc_shift_out_i ? {{QWWidth*2{1'b0}}, adder_res[QWWidth*2+:QWWidth*2]} : adder_res;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      acc_q <= '0;
    end else if (mac_en_i) begin
      acc_q <= acc_d;
    end
  end

  assign res_o = mul_en_i ? {128'b0, mul_res} : adder_res;
endmodule
