// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_shift #(
  parameter int unsigned RegWidth = 256,
  localparam int unsigned ShiftWidth = $clog2(RegWidth)
) (
  input logic [RegWidth-1:0] lower_i,
  input logic [RegWidth-1:0] upper_i,

  input logic shift_left_i,
  input logic [ShiftWidth-1:0] shift_amt_i,

  output logic [RegWidth-1:0] res_o
);
  logic [RegWidth-1:0] lower_reverse;

  logic [RegWidth*2-1:0] shift_in;
  logic [RegWidth*2-1:0] shift_out;
  logic [RegWidth-1:0] shift_out_lower_reverse;

  for (genvar i = 0;i < RegWidth; i++) begin
    assign lower_reverse[i] = lower_i[RegWidth - i - 1];
  end

  assign shift_in = {upper_i, shift_left_i ? lower_reverse : lower_i};

  assign shift_out = shift_in >> shift_amt_i;

  for (genvar i = 0;i < RegWidth; i++) begin
    assign shift_out_lower_reverse[i] = shift_out[RegWidth - i - 1];
  end

  assign res_o = shift_left_i ? shift_out_lower_reverse : shift_out[RegWidth-1:0];
endmodule
