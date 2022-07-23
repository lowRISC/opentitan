// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_loop_controller and used to help collect loop information for coverage.

`include "prim_assert.sv"

interface otbn_loop_if #(
  localparam int LoopStackIdxWidth = prim_util_pkg::vbits(otbn_pkg::LoopStackDepth)
) (
  input              clk_i,
  input              rst_ni,

  // Signal names from the otbn_loop_controller module (where we are bound)
  input logic [31:0] insn_addr_i,
  input logic        at_current_loop_end_insn,
  input logic        current_loop_valid,
  input logic        loop_stack_full,
  input logic        current_loop_finish,
  input logic        next_loop_valid,
  input logic        loop_start_req_i,
  input logic        loop_start_commit_i,
  input logic [31:0] loop_iterations_i,
  input logic        otbn_stall_i,

  input logic [31:0] current_loop_start,
  input logic [31:0] current_loop_end,
  input logic [31:0] next_loop_end,

  input logic [31:0] current_loop_d_iterations,
  input logic [31:0] current_loop_q_iterations,

  input logic [LoopStackIdxWidth-1:0] loop_stack_rd_idx,

  input logic loop_stack_push,
  input logic loop_stack_pop
);

  function automatic otbn_env_pkg::stack_fullness_e get_fullness();
    if (loop_stack_full) begin
      return otbn_env_pkg::StackFull;
    end
    if (current_loop_valid) begin
      return otbn_env_pkg::StackPartial;
    end
    return otbn_env_pkg::StackEmpty;
  endfunction

  // Are assertions in the loop counters currently enabled?
  bit loop_counter_assertions_enabled = 1'b1;

  // Enables or disables all assertions in the loop controller. One assertion in the counter
  // (OutSet_A) is not compatible with loop warping and a more targetted disable for that assertion
  // does not work under Xcelium.
  function automatic void control_loop_counters_out_set_assertion(bit enable);
    if (enable == loop_counter_assertions_enabled) begin
      return;
    end
    if (enable) begin
      $asserton(0, tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller);
    end else begin
      $assertoff(0, tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller);
    end
    loop_counter_assertions_enabled = enable;
  endfunction

  // Track completing some loop. This is implied by the next item, but much easier to hit so maybe
  // worth covering separately.
  `COVER(LoopEnd_C, current_loop_finish)

  // A property that tracks us popping the last loop after we've filled the loop stack. Since we're
  // just using this for coverage, we use first_match on the antecedent to avoid multiple threads if
  // we spend several cycles full.
  `COVER(FullToEmpty_C,
         first_match(loop_stack_full) ##[1:$]
         (current_loop_finish && !next_loop_valid))

  // A property that tracks us completing a one-instruction loop with an iteration count of one (the
  // point being that this is the quickest "in and out"). To spot this happening, we just look for a
  // loop start and then a loop finish on the following cycle.
  `COVER(ShortestLoop_C, (loop_start_req_i && loop_start_commit_i) ##1 current_loop_finish)

  // A property that tracks us running a loop to completion with the maximal number of iterations.
  // (To hit this, we're going to need to force some signals!) This sequence is actually slightly
  // more specific: it asks that this maximal number of iterations should also occur in the
  // innermost loop. This is much easier to track and, in practice, it's going to be the easiest way
  // to try to hit things too.
  `COVER(MaximalLoop_C,
         (loop_start_req_i && loop_start_commit_i && (loop_iterations_i == '1)) ##1
         !(loop_start_req_i && loop_start_commit_i) [*0:$] ##1
         current_loop_finish)

  // Try to see loops with "bad nesting", where the final instruction address for the innermost loop
  // matches the final instruction address for the next one out. This property will trigger on the
  // final instruction of the inner loop for the last time (to make sure we actually get there,
  // where a bug would cause the fireworks).
  `COVER(BadNestingEnd_C,
         current_loop_valid && next_loop_valid &&
         current_loop_finish && (current_loop_end == next_loop_end))

  // Try to see loops with "bad nesting", where the final instruction for an outer loop occurs in
  // the middle of the innermost loop. This property triggers when we execute the instruction at the
  // end of the outer loop (and hopefully nothing exciting happens). We condition this on not
  // stalling (because loop-based redirects only happen when the instruction isn't stalled) but
  // don't condition on next_loop.loop_iterations: even if there are several more iterations left,
  // we'd expect to see a back edge on a spurious match, so it shouldn't matter.
  `COVER(BadNestingMiddle_C,
         current_loop_valid && next_loop_valid &&
         (insn_addr_i != current_loop_end) &&
         (insn_addr_i == next_loop_end) &&
         !otbn_stall_i)

  // Jump into a loop body from outside. We don't bother checking that this is a jump: since the
  // code sequence is fixed, we know we can't get here through a straight line instruction because
  // we check that !loop_start_req_i.
  `COVER(JumpIntoLoop_C,
         (!loop_start_req_i && current_loop_valid &&
          !((current_loop_start <= insn_addr_i) && (insn_addr_i <= current_loop_end))) ##1
         ((current_loop_start <= insn_addr_i) && (insn_addr_i <= current_loop_end)))

  // Jump to the last instruction of a loop body from outside. This is a stronger version of
  // JumpIntoLoop_C.
  `COVER(JumpToLoopEnd_C,
         (!loop_start_req_i && current_loop_valid &&
          !((current_loop_start <= insn_addr_i) && (insn_addr_i <= current_loop_end))) ##1
         (insn_addr_i == current_loop_end))

  // Loop length tracking. If we want to convert between the current "iteration count" as stored by
  // the RTL (which counts down from the initial count to 1) and the iteration count as used in the
  // ISS or spec, we need to know the total number of iterations for this loop. Of course, the RTL
  // doesn't store that (since it doesn't need it), so we have to reconstruct it here.
  logic [31:0] lengths[$];
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lengths.delete();
    end else begin
      if (current_loop_finish && lengths.size()) begin
        void'(lengths.pop_front());
      end
      if (loop_start_req_i && loop_start_commit_i) begin
        lengths.push_front(loop_iterations_i);
      end
    end
  end

  // Convert from the RTL-level view of the iteration counter (starting at the number of iterations
  // and counting down to 1) to the ISA-level view (starting at zero and counting up). If iters is
  // greater than or equal to the surrounding loop count, returns 0: the index of the first
  // iteration.
  function logic [31:0] loop_iters_to_count(logic [31:0] iters);
    if (!lengths.size()) return 0;
    return (iters < lengths[0]) ? lengths[0] - iters : 32'd0;
  endfunction

  // Convert from the ISA-level view (starting at zero and counting up) of the iteration counter to
  // the RTL-level view (starting at the number of iterations and counting down to 1). If count is
  // greater than or equal to the surrounding loop count, returns 1: the index of the last
  // iteration.
  function logic [31:0] loop_count_to_iters(logic [31:0] count);
    if (!lengths.size()) return 0;
    return (count < lengths[0]) ? lengths[0] - count : 32'd1;
  endfunction

endinterface
