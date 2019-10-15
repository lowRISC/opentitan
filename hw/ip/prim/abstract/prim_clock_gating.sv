// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Common Library: Clock Gating cell

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_abstract_pkg::Generic
`endif

module prim_clock_gating (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);

  import prim_abstract_pkg::*;
  localparam int Impl = `PRIM_DEFAULT_IMPL;

  if (Impl == Generic) begin : gen_generic
    prim_generic_clock_gating u_impl_generic (
      .clk_i,
      .en_i,
      .test_en_i,
      .clk_o
    );
  end else if (Impl == Xilinx) begin : gen_xilinx
    prim_xilinx_clock_gating u_impl_xilinx (
      .clk_i,
      .en_i,
      .test_en_i,
      .clk_o
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
