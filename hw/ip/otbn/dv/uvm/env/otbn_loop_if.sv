// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_loop_controller and used to help collect loop information for coverage.

interface otbn_loop_if (
  input              clk_i,
  input              rst_ni,

  input logic [31:0] insn_addr,
  input logic        at_current_loop_end_insn
);

endinterface
