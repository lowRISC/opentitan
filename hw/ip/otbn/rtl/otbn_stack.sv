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
  logic [StackDepthW:0]   stack_wr_ptr, stack_top_idx;
  logic [StackDepthW-1:0] stack_rd_idx, stack_wr_idx;
  logic [StackDepthW:0]   next_stack_top_idx, stack_top_idx_step;
  logic [StackDepthW-1:0] next_stack_rd_idx;

  logic stack_empty;
  logic stack_full;

  logic stack_write;
  logic stack_read;

  assign stack_empty = stack_wr_ptr == '0;
  assign stack_full  = stack_wr_ptr == StackDepth[StackDepthW:0];

  assign stack_write = push_i & (~full_o | pop_i);
  assign stack_read  = top_valid_o & pop_i;

  assign stack_top_idx = stack_wr_ptr[StackDepthW:0];
  assign stack_rd_idx = stack_top_idx[StackDepthW-1:0] - 1'b1;
  assign stack_wr_idx = pop_i ? stack_rd_idx : stack_top_idx[StackDepthW-1:0];

  // This allows us to get around declaring a signed logic, which in turn needs several casts to
  // avoid lint messages.
  localparam logic [StackDepthW:0] Neg1Val = {StackDepthW+1{1'b1}};
  logic [StackDepthW:0] stack_wr_ptr_step;
  always_comb begin
    unique case ({stack_write, stack_read})
      2'b10:   stack_wr_ptr_step = 1;
      2'b01:   stack_wr_ptr_step = Neg1Val; // two's complement representation
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
    if (!(stack_wr_ptr_step inside {Neg1Val, 0, 1})) stack_wr_ptr_step_err_d = 1'b1;
    if (stack_wr_ptr_step == 1 && !stack_write) stack_wr_ptr_step_err_d = 1'b1;
    if (stack_wr_ptr_step == Neg1Val && !stack_read) stack_wr_ptr_step_err_d = 1'b1;
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
    .step_i     (stack_wr_ptr_step),
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

  assign stack_wr_idx_o = stack_wr_idx;
  assign stack_rd_idx_o = stack_rd_idx;
  assign stack_write_o  = stack_write;
  assign stack_read_o   = stack_read;

  always_comb begin
    next_stack_top_idx = '0;
    stack_top_idx_step = '0;

    if (clear_i) begin
      next_stack_top_idx = '0;
    end else begin
      if (stack_wr_ptr_en) begin
        stack_top_idx_step = stack_wr_ptr_step;
      end

      next_stack_top_idx = stack_top_idx + stack_top_idx_step;
    end
  end

  assign next_stack_rd_idx = next_stack_top_idx[StackDepthW-1:0] - 1'b1;

  assign next_top_data_o = stack_write ? push_data_i : stack_storage[next_stack_rd_idx];
  assign next_top_valid_o = next_stack_top_idx != '0;

  `ASSERT(next_stack_top_idx_correct, stack_top_idx == $past(next_stack_top_idx))
endmodule
