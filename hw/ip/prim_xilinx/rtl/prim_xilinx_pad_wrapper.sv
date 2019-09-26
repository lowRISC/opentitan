// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Inferrable, bidirectional IO buffer for FPGAs. Implements inversion and
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
  assign in_o     = inv ^ inout_io;

  // virtual open drain emulation
  logic oe, out;
  assign out      = out_i ^ inv;
  assign oe       = oe_i & ((od & ~out) | ~od);

  // driver
  assign inout_io = (oe) ? out : 1'bz;

endmodule : prim_xilinx_pad_wrapper
