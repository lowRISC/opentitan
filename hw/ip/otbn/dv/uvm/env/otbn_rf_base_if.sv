// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_rf_base and used to help collect call stack information for coverage.

interface otbn_rf_base_if (
  input       clk_i,
  input       rst_ni,

  // Signal names from the otbn_rf_base module (where we are bound)
  input logic pop_stack_a, 
  input logic pop_stack_b,
  input logic push_stack_reqd,
  input logic stack_full,
  input logic stack_data_valid 
);

  function automatic otbn_env_pkg::call_stack_flags_t get_call_stack_flags();
    return '{
              pop_a: pop_stack_a,
              pop_b: pop_stack_b,
              push: push_stack_reqd
            };
  endfunction

  function automatic otbn_env_pkg::stack_fullness_e get_call_stack_fullness();
    if (stack_full) begin
      return otbn_env_pkg::StackFull;
    end
    if (stack_data_valid) begin
      return otbn_env_pkg::StackPartial;
    end
    return otbn_env_pkg::StackEmpty;
  endfunction

endinterface
