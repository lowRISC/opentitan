// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Supports writing a field that enables
// a function within a module.
// Requirements are that the function will
// only be enabled when the field is written
// the it is the inverse of the current field
// setting. The can only toggle between the
// the on value and the off value.


module entropy_src_field_en #(
  parameter int FieldW  = 4,
  parameter int FieldEnVal = 'ha
) (
  input logic clk_i ,
  input logic rst_ni,
  input logic               wvalid_i,
  input logic [FieldW-1:0]  wdata_i,

  output logic              enable_o
);

  // signal
  logic  field_update;
  logic [FieldW-1:0] field_value;
  logic [FieldW-1:0] field_value_invert;

  // flops
  logic [FieldW-1:0] field_q, field_d;

  assign  field_value = FieldEnVal;
  assign  field_value_invert = ~field_value;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      field_q <= field_value_invert;
    end else begin
      field_q <= field_d;
    end
  end

  assign field_update = wvalid_i && (field_q == ~wdata_i) &&
                        ((wdata_i == field_value) ||
                         (wdata_i == field_value_invert));

  assign field_d = field_update ? wdata_i : field_q;

  assign enable_o = (field_q == field_value);


endmodule
