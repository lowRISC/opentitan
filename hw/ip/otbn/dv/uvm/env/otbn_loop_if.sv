// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_loop_controller and used to help collect loop information for coverage.

interface otbn_loop_if (
  input              clk_i,
  input              rst_ni,

  // Signal names from the otbn_loop_controller module (where we are bound)
  input logic [31:0] insn_addr_i,
  input logic        at_current_loop_end_insn,
  input logic        loop_active_q,
  input logic        loop_stack_full,

  input logic [31:0] current_loop_end
);

  function automatic otbn_env_pkg::stack_fullness_e get_fullness();
    if (loop_stack_full) begin
      return otbn_env_pkg::StackFull;
    end
    if (loop_active_q) begin
      return otbn_env_pkg::StackPartial;
    end
    return otbn_env_pkg::StackEmpty;
  endfunction

endinterface
