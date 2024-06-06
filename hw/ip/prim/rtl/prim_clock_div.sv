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
module prim_clock_div

#(

  parameter int unsigned Divisor = 2,
  parameter logic ResetValue = 0

) (
  input clk_i,
  input rst_ni,
  input step_down_req_i, // step down divisor by 2x
  output logic step_down_ack_o, // step down acknowledge
  input test_en_i,
  output logic clk_o
);
  localparam prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

if (Impl == prim_pkg::ImplXilinx_ultrascale) begin : gen_xilinx_ultrascale
    prim_xilinx_ultrascale_clock_div #(
      .Divisor(Divisor),
      .ResetValue(ResetValue)
    ) u_impl_xilinx_ultrascale (
      .*
    );
end else begin : gen_generic
    prim_generic_clock_div #(
      .Divisor(Divisor),
      .ResetValue(ResetValue)
    ) u_impl_generic (
      .*
    );
end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
