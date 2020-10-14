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

  input [ImemAddrWidth-1:0]  insn_addr_i,
  input [ImemAddrWidth-1:0]  next_insn_addr_i,

  input                      loop_start_i,
  input [11:0]               loop_bodysize_i,
  input [31:0]               loop_iterations_i,

  output                     loop_jump_o,
  output [ImemAddrWidth-1:0] loop_jump_addr_o,

  output                     loop_err_o
);
  // The loop controller has a current loop and then a stack of outer loops, this sets the size of
  // the stack so maximum loop nesting depth is LoopStackDepth + 1.
  localparam int unsigned LoopStackDepth = 8;

  typedef struct packed {
    logic [ImemAddrWidth-1:0] loop_start;
    logic [ImemAddrWidth-1:0] loop_end;
    logic [31:0]              loop_iterations;
  } loop_info_t;

  logic       loop_active_q, loop_active_d;
  loop_info_t current_loop_q, current_loop_d;

  logic       at_current_loop_end_insn;
  logic       current_loop_finish;

  loop_info_t next_loop;
  logic       next_loop_valid;

  loop_info_t               new_loop;
  logic [ImemAddrWidth-1:0] new_loop_end_addr;

  logic loop_stack_push;
  logic loop_stack_full;
  logic loop_stack_pop;

  // The loop controller maintains a current loop and a loop stack. The current loop is the
  // innermost loop and is valid when loop_active_q is set. The loop controller tracks the current
  // address vs the current loop end address. When the current loop is active and the end address is
  // reached a jump is performed (via loop_jump_o) back to the top of the loop if iterations of the
  // loop remain. When a new loop is started if a current loop exists it is pushed to the loop
  // stack. When the current loop ends a loop is popped off the loop stack to become the current
  // loop if the loop stack isn't empty.

  // Determine end address of incoming loop from LOOP instruction (valid on loop_start_i and
  // specified by loop_bodysize_i and loop_iterations_i).
  assign new_loop_end_addr = insn_addr_i + {loop_bodysize_i[ImemAddrWidth-3:0], 2'b00};

  assign new_loop = '{
    loop_start: next_insn_addr_i,
    loop_end: new_loop_end_addr,
    loop_iterations: loop_iterations_i
  };

  assign at_current_loop_end_insn = loop_active_q & (current_loop_q.loop_end == insn_addr_i);

  // The iteration decrement happens at loop end. So when execution reaches the end instruction of
  // the current loop with 1 iteration that is the end of the final iteration and the current loop
  // finishes.
  assign current_loop_finish = at_current_loop_end_insn & (current_loop_q.loop_iterations == 1);

  // Jump to top of current loop when execution reaches the end instruction of the current loop it
  // isn't finished.
  assign loop_jump_o      = at_current_loop_end_insn & !current_loop_finish;
  assign loop_jump_addr_o = current_loop_q.loop_start;

  // TODO: Add in loop error conditions
  assign loop_err_o = 1'b0;

  always_comb begin
    loop_active_d  = loop_active_q;
    current_loop_d = current_loop_q;

    if (loop_start_i) begin
      // A new loop is starting (executing LOOP instruction), so incoming loop becomes the current
      // loop
      loop_active_d  = 1'b1;
      current_loop_d = new_loop;
    end else if (current_loop_finish) begin
      // Current loop has finished, check to see if another loop is available on the loop stack
      if (next_loop_valid) begin
        // Loop at top of loop stack (if it exists) becomes the current loop
        current_loop_d = next_loop;
      end else begin
        // Otherwise (loop stack empty) no loop is active.
        loop_active_d = 1'b0;
      end
    end else if (at_current_loop_end_insn) begin
      // Reached end of the current loop so decrement the iteration counter for the current loop
      current_loop_d.loop_iterations = current_loop_q.loop_iterations - 1'b1;
    end
  end

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
  // there is an active loop.
  assign loop_stack_push = loop_start_i & loop_active_q;

  // Pop from the loop stack when the current loop finishes. Stack internally checks to see if it's
  // empty when asked to pop so no need to factor that in here.
  assign loop_stack_pop = current_loop_finish;

  otbn_stack #(
    .StackWidth($bits(loop_info_t)),
    .StackDepth(LoopStackDepth)
  ) loop_info_stack (
    .clk_i,
    .rst_ni,

    .full_o      (loop_stack_full),
    .push_data_i (current_loop_q),
    .push_i      (loop_stack_push),

    .pop_i       (loop_stack_pop),
    .top_data_o  (next_loop),
    .top_valid_o (next_loop_valid)
  );
endmodule
