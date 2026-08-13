// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for rv_timer TB. These properties tackle timer_core
// Intended to be used with a formal tool.
//
// VERIFICATION PLAN
// This module verifies timer_core, which generates periodic tick pulses and
// compares a timer value against N independent compare registers. The tick generator
// increments an internal counter (tick_count) until it equals the prescaler value, then
// generates a tick pulse and resets. 
// The next mtime value (mtime_d) is calculated as mtime + step.   
//
// This module verifies the functionality for a single hart.
// 
// PROPERTIES TO VERIFY
//
// Tick generation 
// - tick is asserted for 1 cycle when tick_count equals prescaler
// - tick_count increments by 1 each cycle when active and less than prescaler
// - tick_count is set to 0 when tick_count equals prescaler
// - when active is low, tick_count and tick are both 0
//
// mtime_d calculation
// - mtime_d is always equal to mtime + step 
// 
// Interrupt generation
// - intr[i] is asserted if active is high and mtime >= mtimecmp[i]
// - intr[i] is low when mtime is less than mtimecmp[i]
// - intr[i] is 0 when active is low
// - intr[i] remains high when mtime >= mtimecmp[i] and active is high
// 
// Reset behaviour
// - when rst_ni is low, tick_count is 0
// - when rst_ni is low, tick is 0


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
