// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.


`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_pad_wrapper #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL,
  parameter int unsigned AttrDw = 6
) (
  inout  wire        inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes
  input [AttrDw-1:0] attr_i
);

  import prim_pkg::*;

  // The generic implementation is NOT synthesizable
  if (Impl == ImplGeneric) begin : gen_pad_generic
    prim_generic_pad_wrapper #(
      .AttrDw(AttrDw)
    ) i_pad_wrapper (
      .inout_io,
      .in_o,
      .out_i,
      .oe_i,
      .attr_i
    );
  end else if (Impl == ImplXilinx) begin : gen_pad_xilinx
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
