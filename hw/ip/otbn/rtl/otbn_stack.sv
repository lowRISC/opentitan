// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Simple stack parameterised on width and depth
 *
 * When a push and pop occur in the same cycle the pop is ordered before the push (so top_data_o
 * reflects what was on top of the stack, which is retrieved by the pop, the push then immediately
 * replaces this with a new piece of data). Internal checking is performed for full & empty
 * conditions so a push on full/pop on empty is allowable, though meaningless. For a push on full
 * the data will be dropped, for a pop no empty there is no valid data to pop. The exception is
 * a combined push & pop on full, here the top is popped off and replaced with what is pushed, no
 * data is dropped.
 *
 * The read and write pointers and read and write signals are exposed as `stack_rd_idx_i,
 * `stack_wr_idx_o`, `stack_write_o` and `stack_read_o`. `next_top_data_o` and `next_top_valid_o`
 * provide the top_data_o and top_valid_o output that will be seen in the following cycle. This is
 * to enable users to extend the stack in case where it's not a simple matter of adding extra data
 * bits (e.g. where this is a prim_count instance per stack entry).
 */
module otbn_stack
  import otbn_pkg::*;
#(
  parameter int unsigned StackWidth = 32,
  parameter int unsigned StackDepth = 4,

  localparam int unsigned StackDepthW = prim_util_pkg::vbits(StackDepth)
) (
  input clk_i,
  input rst_ni,

  output logic                  full_o,      // Stack is full

  output logic                  cnt_err_o,   // Stack counters are wrong

  input logic                   clear_i,     // Clear all data

  input  logic                  push_i,      // Push the data
  input  logic [StackWidth-1:0] push_data_i, // Data to push

  input  logic                  pop_i,       // Pop top of the stack
  output logic [StackWidth-1:0] top_data_o,  // Data on top of the stack
  output logic                  top_valid_o, // Stack is non empty (`top_data_o` is valid)

  output logic [StackDepthW-1:0] stack_wr_idx_o,
  output logic                   stack_write_o,
  output logic [StackDepthW-1:0] stack_rd_idx_o,
  output logic                   stack_read_o,

  output logic [StackWidth-1:0]  next_top_data_o,
  output logic                   next_top_valid_o
);
  logic [StackWidth-1:0]  stack_storage [StackDepth];
  logic [StackDepthW:0]   stack_wr_ptr;
  logic [StackDepthW-1:0] stack_rd_idx, stack_wr_idx;
  logic [StackDepthW:0]   next_stack_wr_ptr;
  logic [StackDepthW-1:0] next_stack_rd_idx;
  logic                   cnt_err, cnt_err_d, cnt_err_q;

  logic stack_empty;
  logic stack_full;

  logic stack_write;
  logic stack_read;

  assign stack_empty = stack_wr_ptr == '0;
  assign stack_full  = stack_wr_ptr == StackDepth[StackDepthW:0];

  assign stack_write = push_i & (~full_o | pop_i);
  assign stack_read  = top_valid_o & pop_i;

  assign stack_rd_idx = stack_wr_ptr[StackDepthW-1:0] - 1'b1;
  assign stack_wr_idx = pop_i ? stack_rd_idx : stack_wr_ptr[StackDepthW-1:0];

  // SEC_CM: STACK_WR_PTR.CTR.REDUN
  prim_count #(
    .Width        (StackDepthW+1)
  ) u_stack_wr_ptr (
    .clk_i,
    .rst_ni,
    .clr_i      (clear_i),
    .set_i      (1'b0),
    .set_cnt_i  ('0),
    .incr_en_i  (stack_write),
    .decr_en_i  (stack_read),
    .step_i     ((StackDepthW+1)'(1'b1)),
    .cnt_o      (stack_wr_ptr),
    .cnt_next_o (next_stack_wr_ptr),
    .err_o      (cnt_err)
  );

  assign cnt_err_d = cnt_err_q | cnt_err;

  prim_flop #(
    .Width(1),
    .ResetValue('0)
  ) u_cnt_err_flop (
    .clk_i,
    .rst_ni,

    .d_i(cnt_err_d),
    .q_o(cnt_err_q)
  );

  assign cnt_err_o = cnt_err_d;

  always_ff @(posedge clk_i) begin
    if (stack_write) begin
      stack_storage[stack_wr_idx] <= push_data_i;
    end
  end


  assign full_o      = stack_full;
  assign top_data_o  = stack_storage[stack_rd_idx];
  assign top_valid_o = ~stack_empty;

  assign stack_wr_idx_o = stack_wr_idx;
  assign stack_rd_idx_o = stack_rd_idx;
  assign stack_write_o  = stack_write;
  assign stack_read_o   = stack_read;

  assign next_stack_rd_idx = next_stack_wr_ptr[StackDepthW-1:0] - 1'b1;

  assign next_top_data_o = stack_write ? push_data_i : stack_storage[next_stack_rd_idx];
  assign next_top_valid_o = next_stack_wr_ptr != '0;

endmodule
