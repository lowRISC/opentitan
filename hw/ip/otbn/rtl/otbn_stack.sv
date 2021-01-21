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
 */
module otbn_stack
  import otbn_pkg::*;
#(
  parameter int unsigned StackWidth = 32,
  parameter int unsigned StackDepth = 4
) (
  input clk_i,
  input rst_ni,

  output logic                  full_o,      // Stack is full

  input  logic                  push_i,      // Push the data
  input  logic [StackWidth-1:0] push_data_i, // Data to push

  input  logic                  pop_i,       // Pop top of the stack
  output logic [StackWidth-1:0] top_data_o,  // Data on top of the stack
  output logic                  top_valid_o  // Stack is non empty (`top_data_o` is valid)
);

  localparam int unsigned StackDepthW = prim_util_pkg::vbits(StackDepth);

  logic [StackWidth-1:0]  stack_storage [StackDepth];
  logic [StackDepthW:0]   stack_wr_ptr_q, stack_wr_ptr_d;
  logic [StackDepthW-1:0] stack_top_idx, stack_rd_idx, stack_wr_idx;

  logic stack_empty;
  logic stack_full;

  logic stack_write;
  logic stack_read;

  assign stack_empty = stack_wr_ptr_q == '0;
  assign stack_full  = stack_wr_ptr_q == StackDepth[StackDepthW:0];

  assign stack_write = push_i & (~full_o | pop_i);
  assign stack_read  = top_valid_o & pop_i;

  assign stack_top_idx = stack_wr_ptr_q[StackDepthW-1:0];
  assign stack_rd_idx = stack_top_idx - 1'b1;
  assign stack_wr_idx = pop_i ? stack_rd_idx : stack_top_idx;

  always_comb begin
    stack_wr_ptr_d = stack_wr_ptr_q;

    if (stack_write && !stack_read) begin
      stack_wr_ptr_d = stack_wr_ptr_q + 1'b1;
    end

    if (!stack_write && stack_read) begin
      stack_wr_ptr_d = stack_wr_ptr_q - 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stack_wr_ptr_q <= '0;
    end else begin
      stack_wr_ptr_q <= stack_wr_ptr_d;
    end
  end

  always_ff @(posedge clk_i) begin
    if (stack_write) begin
      stack_storage[stack_wr_idx] <= push_data_i;
    end
  end

  assign full_o      = stack_full;
  assign top_data_o  = stack_storage[stack_rd_idx];
  assign top_valid_o = ~stack_empty;
endmodule
