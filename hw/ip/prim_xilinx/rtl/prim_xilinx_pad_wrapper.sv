// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bidirectional IO buffer for Xilinx FPGAs. Implements inversion and
// virtual open drain feature.


module prim_xilinx_pad_wrapper #(
  parameter int unsigned AttrDw = 2
) (
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes
  input [AttrDw-1:0] attr_i
);

  // get pad attributes
  logic od, inv;
  assign {od, inv} = attr_i[1:0];

  // input inversion
  logic in;
  assign in_o     = inv ^ in;

  // virtual open drain emulation
  logic oe_n, out;
  assign out      = out_i ^ inv;
  // oe_n = 0: enable driver
  // oe_n = 1: disable driver
  assign oe_n     = ~oe_i | (out & od);

  // driver
  IOBUF i_iobuf (
    .T(oe_n),
    .I(out),
    .O(in),
    .IO(inout_io)
  );

endmodule : prim_xilinx_pad_wrapper
