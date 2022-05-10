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

  output logic                  cnt_err_o,   // Stack counters are wrong

  input logic                   clear_i,     // Clear all data

  input  logic                  push_i,      // Push the data
  input  logic [StackWidth-1:0] push_data_i, // Data to push

  input  logic                  pop_i,       // Pop top of the stack
  output logic [StackWidth-1:0] top_data_o,  // Data on top of the stack
  output logic                  top_valid_o  // Stack is non empty (`top_data_o` is valid)
);

  localparam int unsigned StackDepthW = prim_util_pkg::vbits(StackDepth);

  logic [StackWidth-1:0]  stack_storage [StackDepth];
  logic [StackDepthW:0]   stack_wr_ptr;
  logic [StackDepthW-1:0] stack_top_idx, stack_rd_idx, stack_wr_idx;

  logic stack_empty;
  logic stack_full;

  logic stack_write;
  logic stack_read;

  assign stack_empty = stack_wr_ptr == '0;
  assign stack_full  = stack_wr_ptr == StackDepth[StackDepthW:0];

  assign stack_write = push_i & (~full_o | pop_i);
  assign stack_read  = top_valid_o & pop_i;

  assign stack_top_idx = stack_wr_ptr[StackDepthW-1:0];
  assign stack_rd_idx = stack_top_idx - 1'b1;
  assign stack_wr_idx = pop_i ? stack_rd_idx : stack_top_idx;

  logic signed [StackDepthW:0] stack_wr_ptr_step;
  always_comb begin
    unique case ({stack_write, stack_read})
      2'b10:   stack_wr_ptr_step = 1;
      2'b01:   stack_wr_ptr_step = -1;
      default: stack_wr_ptr_step = '0;
    endcase
  end

  // SEC_CM: STACK_WR_PTR.CTR.GLITCH_DETECT
  // Detect glitches on the `step_i` input of the stack write pointer.  If a glitch is detected,
  // latch it until the stack gets cleared (or the module is reset).  Detecting glitches on the
  // clock edge instead of combinationally is required because the error output drives the control
  // path, thus feeding the glitch detector output back combinationally would result in
  // combinational loops.
  logic stack_wr_ptr_step_err_d, stack_wr_ptr_step_err_q;
  always_comb begin
    stack_wr_ptr_step_err_d = stack_wr_ptr_step_err_q;
    if (clear_i) stack_wr_ptr_step_err_d = 1'b0;
    if (stack_wr_ptr_step > 1 || stack_wr_ptr_step < -1) stack_wr_ptr_step_err_d = 1'b1;
    if (stack_wr_ptr_step == 1 && !stack_write) stack_wr_ptr_step_err_d = 1'b1;
    if (stack_wr_ptr_step == -1 && !stack_read) stack_wr_ptr_step_err_d = 1'b1;
    if (stack_wr_ptr_step == 0 && (stack_write ^ stack_read)) stack_wr_ptr_step_err_d = 1'b1;
  end

  logic stack_wr_ptr_step_err_buf;
  prim_buf #(
    .Width (1)
  ) u_stack_wr_ptr_step_err_buf (
    .in_i   (stack_wr_ptr_step_err_d),
    .out_o  (stack_wr_ptr_step_err_buf)
  );

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      stack_wr_ptr_step_err_q <= 1'b0;
    end else begin
      stack_wr_ptr_step_err_q <= stack_wr_ptr_step_err_buf;
    end
  end

  logic stack_wr_ptr_en;
  assign stack_wr_ptr_en = stack_wr_ptr_step != '0;

  // SEC_CM: STACK_WR_PTR.CTR.REDUN
  logic stack_wr_ptr_err;
  prim_count #(
    .Width        (StackDepthW+1),
    .OutSelDnCnt  (0),
    .CntStyle     (prim_count_pkg::DupCnt)
  ) u_stack_wr_ptr (
    .clk_i,
    .rst_ni,
    .clr_i      (clear_i),
    .set_i      (1'b0),
    .set_cnt_i  ('0),
    .en_i       (stack_wr_ptr_en),
    // Since this signal has the same width as the counter, negative values will
    // be correctly be subtracted due to the 2s complement representation.
    .step_i     (unsigned'(stack_wr_ptr_step)),
    .cnt_o      (stack_wr_ptr),
    .err_o      (stack_wr_ptr_err)
  );

  always_ff @(posedge clk_i) begin
    if (stack_write) begin
      stack_storage[stack_wr_idx] <= push_data_i;
    end
  end

  assign full_o      = stack_full;
  assign top_data_o  = stack_storage[stack_rd_idx];
  assign top_valid_o = ~stack_empty;
  assign cnt_err_o   = stack_wr_ptr_err | stack_wr_ptr_step_err_q;
endmodule
