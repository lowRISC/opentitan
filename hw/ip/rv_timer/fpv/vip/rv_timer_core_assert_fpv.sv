// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for rv_timer TB. These properties tackle timer_core
// Intended to be used with a formal tool.

module rv_timer_core_assert_fpv # (
  parameter int N
) (
  input logic         clk_i,
  input logic         rst_ni,

  input logic         active,
  input logic [11:0]  prescaler,
  input logic [ 7:0]  step,

  input logic         tick,
  input logic [63:0]  mtime_d,
  input logic [63:0]  mtime,
  input logic [63:0]  mtimecmp [N],

  input logic [N-1:0] intr
);

  // TODO: populate me with FPV

endmodule
