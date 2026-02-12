// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions that can be bound in to an instance of the prim_diff_decode module

module prim_diff_decode_assert_fpv #(
  parameter bit AsyncOn = 1'b0
) (
  input        clk_i,
  input        rst_ni
);
  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;

  if (AsyncOn) begin : gen_async_assertions
    // There are three valid states for the FSM and we never expect it to get to the other value in
    // the 2-bit encoding.
    ValidState_A: assert property (gen_async.state_q inside {gen_async.IsStd,
                                                             gen_async.IsSkewing,
                                                             gen_async.SigInt});
  end
endmodule
