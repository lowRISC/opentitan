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

  // Default statements:
  default disable iff (!rst_ni || !active);
  default clocking @(posedge clk_i); endclocking

  // Glue logic for the prescaler counter:
  logic [11:0] prescaler_count;
  logic        limit_reached;
  always_ff @(posedge clk_i or negedge rst_ni) begin: prescaler_counter
    if (!rst_ni || !active || prescaler_count == prescaler)
      prescaler_count <= 0;
    else
      prescaler_count <= prescaler_count + 1'b1;
  end
  assign limit_reached = prescaler_count == prescaler;
  // Don't allow prescaler/step/mtimecmp to change on the fly while active is set
  ActiveImpliesConfigStable_A : assume property ($stable({prescaler, step}) && $stable(mtimecmp));

  // Verify tick_count counter:
  // Timer increases
  property CountIncreases_p;
    prescaler_count < prescaler |=> (prescaler_count == $past(prescaler_count) + 1);
  endproperty
  TickCountIncreases_A : assert property (CountIncreases_p);

  // Tick set means prescaler equals the count.
  // TickSet_A checks that if the RTL has tick set, then our internal logic must be equal to the
  // prescaler max and vice-versa
  TickSet_A: assert property (limit_reached iff tick);
  // Helper property to help tool converge in above property more quickly by checking the internal
  // count is equal to RTL count
  TickSetHelper_A:
    assert property (disable iff (!rst_ni) prescaler_count == gen_harts[0].u_core.tick_count);
  // Note: Jasper doesn't autogenerate a cover property when using `iff` operator
  TickSet_C: cover property (tick);

  // Tick count reset:
  TickCountActiveReset_A: assert property ($rose(active) |-> prescaler_count == 0);
  // If we were active before, and the count equals the prescaler then the count should be
  // reset to zero
  property PrescalerMaxReset_p;
    (prescaler_count == prescaler) |=> prescaler_count == 0;
  endproperty
  TickCountPrescalerMaxReset_A: assert property (PrescalerMaxReset_p);

  // Free variable to avoid having to declare a generate block and hence proving faster
  int unsigned fpv_timer_idx;
  // Free variable constraints:
  // - Lower than N
  // - Can't change every time active is set
  FreeIndexVariableMaxValue_A: assume property (fpv_timer_idx < N);
  FreeIndexVariableStable_A: assume property ($stable(fpv_timer_idx));

  // Force Mtime to be $past(mtime) + step when inrementing
  MtimeChangesInStepIncrements_A:
    assume property ($changed(mtime) |-> $past(tick) && ($past(mtime) + $past(step)) == mtime);

  // Checks whether an interrupt raises during active being set. This means that the internal
  // prescaler has saturated and mtime has increased causing it to be greater than or equal
  // to mtimecmp
  property InterruptRaiseWhilstActive_p;
    $past(active) && $rose(intr[fpv_timer_idx]) |->
      $past(tick) && ($past(mtime) + $past(step)) >= mtimecmp[fpv_timer_idx];
  endproperty
  InterruptRaiseWhilstActive_A: assert property (InterruptRaiseWhilstActive_p);

  // Checks whether mtime is greater than or equal to mtimecmp as soon as active and interrupt
  // raise
  property InterruptRaiseAndActiveRaise_p;
    $rose(active) && $rose(intr[fpv_timer_idx]) |-> mtime >= mtimecmp[fpv_timer_idx];
  endproperty
  InterruptRaiseAndActiveRaise_A: assert property (InterruptRaiseAndActiveRaise_p);
endmodule
