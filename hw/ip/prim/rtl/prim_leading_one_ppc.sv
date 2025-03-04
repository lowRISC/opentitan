// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Leading one detector based on parallel prefix computation
// See also: prim_arbiter_ppc

module prim_leading_one_ppc #(
  parameter int unsigned N = 8,
  localparam int IdxW      = prim_util_pkg::vbits(N)
) (
  input        [ N-1:0]    in_i,
  output logic [ N-1:0]    leading_one_o,
  output logic [ N-1:0]    ppc_out_o,
  output logic [IdxW-1:0]  idx_o
);
  logic [N-1:0] ppc_out;

  // PPC
  //   Even below code looks O(n) but DC optimizes it to O(log(N))
  //   Using Parallel Prefix Computation
  always_comb begin
    ppc_out[0] = in_i[0];
    for (int i = 1 ; i < N ; i++) begin
      ppc_out[i] = ppc_out[i-1] | in_i[i];
    end
  end

  // Leading-One detector
  assign leading_one_o = ppc_out ^ {ppc_out[N-2:0], 1'b0};
  assign ppc_out_o     = ppc_out;

  always_comb begin
    idx_o = '0;
    for (int unsigned i = 0 ; i < N ; i++) begin
      if (leading_one_o[i]) begin
        idx_o = i[IdxW-1:0];
      end
    end
  end

endmodule
