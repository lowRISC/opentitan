// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_loop_controller
  import otbn_pkg::*;
#(
  parameter int ImemAddrWidth = 12
) (
  input clk_i,
  input rst_ni,

  input state_reset_i,

  input                     insn_valid_i,
  input [ImemAddrWidth-1:0] insn_addr_i,
  input [ImemAddrWidth-1:0] next_insn_addr_i,

  input        loop_start_req_i,
  input        loop_start_commit_i,
  input [11:0] loop_bodysize_i,
  input [31:0] loop_iterations_i,

  output                     loop_jump_o,
  output [ImemAddrWidth-1:0] loop_jump_addr_o,

  output sw_err_o,
  output hw_err_o,

  output                     prefetch_loop_active_o,
  output [31:0]              prefetch_loop_iterations_o,
  output [ImemAddrWidth:0]   prefetch_loop_end_addr_o,
  output [ImemAddrWidth-1:0] prefetch_loop_jump_addr_o,

  input jump_or_branch_i,
  input otbn_stall_i
);
  // The loop controller has a current loop and then a stack of outer loops, this sets the size of
  // the stack so maximum loop nesting depth is LoopStackDepth + 1.
  localparam int unsigned LoopStackDepth = 7;

  // The ISA has a fixed 12 bits for loop_bodysize. The maximum possible address for the end of a
  // loop is the maximum address in Imem (2^ImemAddrWidth - 4) plus loop_bodysize instructions
  // (which take 4 * (2^12 - 1) bytes), plus 4 extra bytes. This simplifies to
  //
  //    (1 << ImemAddrWidth) + (1 << 14) - 4
  //
  // which is strictly less than (1 << (max(ImemAddrWidth, 14) + 1)), so can be represented with
  // max(ImemAddrWidth, 14) + 1 bits.
  localparam int unsigned LoopEndAddrWidth = 1 + (ImemAddrWidth < 14 ? 14 : ImemAddrWidth);

  typedef struct packed {
    logic [ImemAddrWidth-1:0] loop_start;
    logic [ImemAddrWidth:0]   loop_end;
    logic [31:0]              loop_iterations;
  } loop_info_t;

  logic       loop_active_q, loop_active_d;
  loop_info_t current_loop_q, current_loop_d;

  logic       at_current_loop_end_insn;
  logic       current_loop_finish;

  loop_info_t next_loop;
  logic       next_loop_valid;

  loop_info_t                  new_loop;
  logic [LoopEndAddrWidth-1:0] new_loop_end_addr_full;
  logic [ImemAddrWidth:0]      new_loop_end_addr_imem;

  logic loop_stack_push_req;
  logic loop_stack_push;
  logic loop_stack_full;
  logic loop_stack_pop;

  logic loop_iteration_err;
  logic loop_branch_err;
  logic loop_stack_overflow_err;
  logic loop_at_end_err;

  // The loop controller maintains a current loop and a loop stack. The current loop is the
  // innermost loop and is valid when loop_active_q is set. The loop controller tracks the current
  // address vs the current loop end address. When the current loop is active and the end address is
  // reached a jump is performed (via loop_jump_o) back to the top of the loop if iterations of the
  // loop remain. When a new loop is started if a current loop exists it is pushed to the loop
  // stack. When the current loop ends a loop is popped off the loop stack to become the current
  // loop if the loop stack isn't empty.

  // Determine end address of incoming loop from LOOP/LOOPI instruction (valid on loop_start_req_i
  // and specified by the current instruction address and loop_bodysize_i).
  //
  // Note that both of the static casts increase the size of their terms because LoopEndAddrWidth >
  // max(14, ImemAddrWidth).
  assign new_loop_end_addr_full = LoopEndAddrWidth'(insn_addr_i) +
                                  LoopEndAddrWidth'({loop_bodysize_i, 2'b00}) + 'd4;

  // Truncate the full address to get an Imem address.
  assign new_loop_end_addr_imem[ImemAddrWidth-1:0] = new_loop_end_addr_full[ImemAddrWidth-1:0];

  // If the end address calculation overflowed ImemAddrWidth, set top bit of stored end address to
  // indicate this.
  assign new_loop_end_addr_imem[ImemAddrWidth] =
      |new_loop_end_addr_full[LoopEndAddrWidth-1:ImemAddrWidth];

  assign new_loop = '{
    loop_start: next_insn_addr_i,
    loop_end: new_loop_end_addr_imem,
    loop_iterations: loop_iterations_i
  };

  // `loop_end` has one more bit than Imem width; this is set when the end address calculation
  // overflows. When this is the case the end instruction is never reached.
  assign at_current_loop_end_insn =
      loop_active_q & (current_loop_q.loop_end == {1'b0, insn_addr_i}) & insn_valid_i;

  // The iteration decrement happens at loop end. So when execution reaches the end instruction of
  // the current loop with 1 iteration that is the end of the final iteration and the current loop
  // finishes.
  assign current_loop_finish = at_current_loop_end_insn & (current_loop_q.loop_iterations == 1)
    & ~otbn_stall_i;

  // Jump to top of current loop when execution reaches the end instruction of the current loop it
  // isn't finished.
  assign loop_jump_o      = at_current_loop_end_insn & ~current_loop_finish;
  assign loop_jump_addr_o = current_loop_q.loop_start;

  assign loop_iteration_err      = (loop_iterations_i == '0) & loop_start_req_i;
  assign loop_branch_err         = at_current_loop_end_insn & jump_or_branch_i;
  assign loop_stack_overflow_err = loop_stack_push_req & loop_stack_full;
  assign loop_at_end_err         = at_current_loop_end_insn & loop_start_req_i;

  assign sw_err_o = loop_iteration_err      |
                    loop_branch_err         |
                    loop_stack_overflow_err |
                    loop_at_end_err;

  always_comb begin
    loop_active_d  = loop_active_q;
    current_loop_d = current_loop_q;

    if (state_reset_i) begin
      // Clear any current loop on start
      loop_active_d = 1'b0;
    end else if (!otbn_stall_i) begin
      // If we're not starting a new operation, we only take state altering actions if OTBN is not
      // stalled.

      if (loop_start_req_i && loop_start_commit_i) begin
        // A new loop is starting (executing LOOP instruction), so incoming loop becomes the current
        // loop.
        loop_active_d  = 1'b1;
        current_loop_d = new_loop;
      end else if (current_loop_finish) begin
        // Current loop has finished, check to see if another loop is available on the loop stack.
        if (next_loop_valid) begin
          // Loop at top of loop stack (if it exists) becomes the current loop.
          current_loop_d = next_loop;
        end else begin
          // Otherwise (loop stack empty) no loop is active.
          loop_active_d = 1'b0;
        end
      end else if (at_current_loop_end_insn) begin
        // Reached end of the current loop so decrement the iteration counter for the current loop.
        current_loop_d.loop_iterations = current_loop_q.loop_iterations - 1'b1;
      end
    end
  end

  // The OTBN controller must not commit a loop request if it sees a loop error.
  `ASSERT(NoStartCommitIfLoopErr, loop_start_req_i && loop_start_commit_i |-> !sw_err_o)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      loop_active_q <= 1'b0;
    end else begin
      loop_active_q <= loop_active_d;
    end
  end

  always_ff @(posedge clk_i) begin
    current_loop_q <= current_loop_d;
  end

  // Push current loop to the loop stack when a new loop starts (LOOP instruction executed) and
  // there is an active loop. loop_stack_push_req indicates a push is requested and loop_stack_push
  // commands it to happen (when the loop start is committed).
  assign loop_stack_push_req = loop_start_req_i & loop_active_q;
  assign loop_stack_push     = loop_start_commit_i & loop_stack_push_req;

  // Pop from the loop stack when the current loop finishes. Stack internally checks to see if it's
  // empty when asked to pop so no need to factor that in here.
  assign loop_stack_pop = current_loop_finish;

  otbn_stack #(
    .StackWidth($bits(loop_info_t)),
    .StackDepth(LoopStackDepth)
  ) loop_info_stack (
    .clk_i,
    .rst_ni,

    .full_o(loop_stack_full),

    .cnt_err_o(hw_err_o),

    .clear_i(state_reset_i),

    .push_data_i(current_loop_q),
    .push_i     (loop_stack_push),

    .pop_i      (loop_stack_pop),
    .top_data_o (next_loop),
    .top_valid_o(next_loop_valid)
  );

  // Forward info about loop state for next cycle to prefetch stage
  assign prefetch_loop_active_o     = loop_active_d;
  assign prefetch_loop_iterations_o = current_loop_d.loop_iterations;
  assign prefetch_loop_end_addr_o   = current_loop_d.loop_end;
  assign prefetch_loop_jump_addr_o  = current_loop_d.loop_start;

  `ASSERT(NoLoopStackPushAndPop, !(loop_stack_push && loop_stack_pop))
endmodule
