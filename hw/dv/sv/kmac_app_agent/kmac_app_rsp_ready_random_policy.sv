// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Randomized response backpressure policy.
//
// This policy models a response channel that does not accept data immediately after every valid
// response. Instead, it deliberately inserts random backpressure for a bounded number of cycles, then
// eventually forces the interface to accept the response so the transaction can continue. This is
// useful for stress-testing the host-side driver and scoreboard
// while still guaranteeing recovery from a stall condition.
class kmac_app_rsp_ready_random_policy extends kmac_app_rsp_ready_policy;
  `uvm_object_utils(kmac_app_rsp_ready_random_policy)

  // Consecutive cycles stalled for the current response.
  int unsigned stall_cycles;

  extern function new(string name = "");
  extern virtual function void reset();
  extern virtual function bit get_rsp_ready(bit rsp_valid,
                                            int unsigned ready_pct,
                                            int unsigned max_stall_cycles);
endclass

function kmac_app_rsp_ready_random_policy::new(string name = "");
  super.new(name);
endfunction

// Reset the random backpressure state on reset or when a new response burst starts.
function void kmac_app_rsp_ready_random_policy::reset();
  stall_cycles = 0;
endfunction

// Randomly stall valid responses up to max_stall_cycles.
function bit kmac_app_rsp_ready_random_policy::get_rsp_ready(bit rsp_valid,
                                                             int unsigned ready_pct,
                                                             int unsigned max_stall_cycles);
  bit ready;

  if (!rsp_valid) begin
    stall_cycles = 0;
    return 1'b0;
  end

  // Force ready after the maximum stall count.
  if (stall_cycles >= max_stall_cycles) begin
    stall_cycles = 0;
    return 1'b1;
  end

  // Use ready_pct as the acceptance probability.
  ready = $urandom_range(0, 99) < ready_pct;

  // Reset after acceptance; otherwise extend the stall.
  stall_cycles = ready ? 0 : stall_cycles + 1;
  return ready;
endfunction
