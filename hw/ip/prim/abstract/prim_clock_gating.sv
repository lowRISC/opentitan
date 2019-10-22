// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_clock_gating #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL
) (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);

  import prim_pkg::*;

  if (Impl == ImplGeneric) begin : gen_generic
    prim_generic_clock_gating u_impl_generic (
      .clk_i,
      .en_i,
      .test_en_i,
      .clk_o
    );
  end else if (Impl == ImplXilinx) begin : gen_xilinx
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
