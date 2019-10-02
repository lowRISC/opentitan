// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

// prim_pad_wrapper using the generic implementation
module prim_pad_wrapper #(
  parameter              Impl   = "generic",
  parameter int unsigned AttrDw = 6
) (
  inout  wire        inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes
  input [AttrDw-1:0] attr_i
);

  // The generic implementation is NOT synthesizable
  if (Impl == "generic") begin : gen_pad_generic
    prim_generic_pad_wrapper #(
      .AttrDw(AttrDw)
    ) i_pad_wrapper (
      .inout_io,
      .in_o,
      .out_i,
      .oe_i,
      .attr_i
    );
  end else if (Impl == "xilinx") begin : gen_pad_xilinx
    prim_xilinx_pad_wrapper #(
      .AttrDw(AttrDw)
    ) i_pad_wrapper (
      .inout_io,
      .in_o,
      .out_i,
      .oe_i,
      .attr_i
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule : prim_pad_wrapper
