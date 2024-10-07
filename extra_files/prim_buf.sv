// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.
// Used parser: Fallback (regex)

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

// This is to prevent AscentLint warnings in the generated
// abstract prim wrapper. These warnings occur due to the .*
// use. TODO: we may want to move these inline waivers
// into a separate, generated waiver file for consistency.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
module prim_buf

#(

  parameter int Width = 1

) (
  input        [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);
  localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    prim_xilinx_buf #(
      .Width(Width)
    ) u_impl_xilinx (
      .*
    );
end else if (Impl == prim_pkg::ImplXilinx_ultrascale) begin : gen_xilinx_ultrascale
    prim_xilinx_ultrascale_buf #(
      .Width(Width)
    ) u_impl_xilinx_ultrascale (
      .*
    );
end else begin : gen_generic
    prim_generic_buf #(
      .Width(Width)
    ) u_impl_generic (
      .*
    );
end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
