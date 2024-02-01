// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Protocol checker for multiple TL-UL ports

module tlul_assert_multiple #(
  parameter int unsigned N = 2,
  parameter EndpointType = "Device" // can be "Device" or "Host"
) (
  input clk_i,
  input rst_ni,

  // tile link ports
  input tlul_pkg::tl_h2d_t h2d [N],
  input tlul_pkg::tl_d2h_t d2h [N]
);

  // instantiate N tlul_assert modules
  for (genvar ii = 0; ii < N; ii++) begin : gen_assert
    tlul_assert #(
      .EndpointType(EndpointType)
    ) tlul_assert (
      .clk_i,
      .rst_ni,
      // TL-UL ports
      .h2d (h2d[ii]),
      .d2h (d2h[ii])
    );
  end
endmodule
