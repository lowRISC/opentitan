// Copyright lowRISC contributors (OpenTitan project).
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

  localparam logic [FieldW-1:0] FieldEnValBit = FieldW'(FieldEnVal);
  localparam logic [FieldW-1:0] FieldEnValBitRevert = ~FieldEnValBit;

  // signal
  logic  field_update;

  // flops
  logic [FieldW-1:0] field_q, field_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      field_q <= FieldEnValBitRevert;
    end else begin
      field_q <= field_d;
    end
  end

  assign field_update = wvalid_i && (field_q == ~wdata_i) &&
                        ((wdata_i == FieldEnValBit) ||
                         (wdata_i == FieldEnValBitRevert));

  assign field_d = field_update ? wdata_i : field_q;

  assign enable_o = (field_q == FieldEnValBit);


endmodule
