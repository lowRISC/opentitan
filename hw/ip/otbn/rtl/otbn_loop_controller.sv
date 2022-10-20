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

  input                     loop_start_req_i,
  input                     loop_start_commit_i,
  input [11:0]              loop_bodysize_i,
  input [31:0]              loop_iterations_i,
  input [ImemAddrWidth-1:0] loop_end_addr_predec_i,

  output                     loop_jump_o,
  output [ImemAddrWidth-1:0] loop_jump_addr_o,

  output sw_err_o,
  output hw_err_o,
  output predec_err_o,

  output                     prefetch_loop_active_o,
  output [31:0]              prefetch_loop_iterations_o,
  output [ImemAddrWidth:0]   prefetch_loop_end_addr_o,
  output [ImemAddrWidth-1:0] prefetch_loop_jump_addr_o,

  input jump_or_branch_i,
  input otbn_stall_i
);
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
    logic [6:0]               loop_addrs_intg;
  } loop_addr_info_t;

  typedef struct packed {
    loop_addr_info_t          loop_addr_info;
    logic [31:0]              loop_iterations;
  } loop_info_t;

  loop_info_t current_loop;
  logic       current_loop_valid;

  logic        at_current_loop_end_insn;
  logic        current_loop_finish;
  logic        current_loop_counter_dec;
  logic [38:0] current_loop_addrs_padded_intg_unbuf, current_loop_addrs_padded_intg_buf;
  logic [1:0]  current_loop_intg_err;

  loop_info_t                  new_loop;
  logic [LoopEndAddrWidth-1:0] new_loop_end_addr_full;
  logic [ImemAddrWidth:0]      new_loop_end_addr_imem;
  logic [31:0]                 new_loop_addrs_padded_no_intg;
  logic [38:0]                 new_loop_addrs_padded_intg;

  loop_addr_info_t             next_loop_addr_info;
  logic                        next_loop_valid;
  logic loop_stack_push_req;
  logic loop_stack_push;
  logic loop_stack_full;
  logic loop_stack_pop;

  logic loop_iteration_err;
  logic loop_branch_err;
  logic loop_stack_overflow_err;
  logic loop_at_end_err;
  logic loop_stack_cnt_err;

  localparam int unsigned StackDepthW = prim_util_pkg::vbits(LoopStackDepth);
  logic [StackDepthW-1:0] loop_stack_wr_idx;
  logic                   loop_stack_write;
  logic [StackDepthW-1:0] loop_stack_rd_idx;

  logic [31:0]               loop_counters [LoopStackDepth];
  logic [LoopStackDepth-1:0] loop_counter_err, loop_counter_err_d, loop_counter_err_q;

  // The loop controller maintains a loop stack. The top of the loop stack is the innermost loop and
  // is valid when current_loop_valid is set. The loop controller tracks the current address vs the
  // current loop end address. When the current loop is active and the end address is reached a jump
  // is performed (via loop_jump_o) back to the top of the loop if iterations of the loop remain.
  // When a new loop is started it is pushed to the loop stack. When the current loop ends it is
  // popped off the loop stack with the loop below it becoming the current loop if the loop stack
  // isn't empty.

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

  assign new_loop_addrs_padded_no_intg = {{(32 - (ImemAddrWidth * 2) - 1){1'b0}},
                                          next_insn_addr_i,
                                          new_loop_end_addr_imem};

  prim_secded_inv_39_32_enc u_new_loop_addrs_intg_enc (
    .data_i(new_loop_addrs_padded_no_intg),
    .data_o(new_loop_addrs_padded_intg)
  );

  logic unused_new_loop_addrs_padded_intg;
  assign unused_new_loop_addrs_padded_intg = ^new_loop_addrs_padded_intg[31:0];

  assign new_loop = '{
    loop_addr_info : '{
        loop_start:      next_insn_addr_i,
        loop_end:        new_loop_end_addr_imem,
        loop_addrs_intg: new_loop_addrs_padded_intg[38:32]
    },
    loop_iterations: loop_iterations_i
  };

  // `loop_end` has one more bit than Imem width; this is set when the end address calculation
  // overflows. When this is the case the end instruction is never reached.
  assign at_current_loop_end_insn =
      current_loop_valid & (current_loop.loop_addr_info.loop_end == {1'b0, insn_addr_i}) &
      insn_valid_i;

  // The iteration decrement happens at loop end. So when execution reaches the end instruction of
  // the current loop with 1 iteration that is the end of the final iteration and the current loop
  // finishes.
  assign current_loop_finish = at_current_loop_end_insn & (current_loop.loop_iterations == 1)
    & ~otbn_stall_i;

  // Jump to top of current loop when execution reaches the end instruction of the current loop it
  // isn't finished.
  assign loop_jump_o      = at_current_loop_end_insn & ~current_loop_finish;
  assign loop_jump_addr_o = current_loop.loop_addr_info.loop_start;

  assign loop_iteration_err      = (loop_iterations_i == '0) & loop_start_req_i;
  assign loop_branch_err         = at_current_loop_end_insn & jump_or_branch_i;
  assign loop_stack_overflow_err = loop_stack_push_req & loop_stack_full;
  assign loop_at_end_err         = at_current_loop_end_insn & loop_start_req_i;

  assign sw_err_o = loop_iteration_err      |
                    loop_branch_err         |
                    loop_stack_overflow_err |
                    loop_at_end_err;

  // Decrement current loop counter when execution reaches the end instruction
  assign current_loop_counter_dec = ~state_reset_i & ~otbn_stall_i & at_current_loop_end_insn;

  assign loop_stack_push_req = loop_start_req_i;

  // The OTBN controller must not commit a loop request if it sees a loop error.
  `ASSERT(NoStartCommitIfLoopErr, loop_start_req_i && loop_start_commit_i |-> !sw_err_o)

  // Push current loop to the loop stack when a new loop starts (LOOP instruction executed).
  // loop_stack_push_req indicates a push is requested and loop_stack_push commands it to happen
  // (when the loop start is committed).
  assign loop_stack_push = loop_start_commit_i & loop_stack_push_req;

  // Pop from the loop stack when the current loop finishes. Stack internally checks to see if it's
  // empty when asked to pop so no need to factor that in here.
  assign loop_stack_pop = current_loop_finish;

  otbn_stack #(
    .StackWidth($bits(loop_addr_info_t)),
    .StackDepth(LoopStackDepth)
  ) loop_info_stack (
    .clk_i,
    .rst_ni,

    .full_o(loop_stack_full),

    .cnt_err_o(loop_stack_cnt_err),

    .clear_i(state_reset_i),

    .push_data_i(new_loop.loop_addr_info),
    .push_i     (loop_stack_push),

    .pop_i      (loop_stack_pop),
    .top_data_o (current_loop.loop_addr_info),
    .top_valid_o(current_loop_valid),

    .stack_wr_idx_o(loop_stack_wr_idx),
    .stack_write_o (loop_stack_write),
    .stack_rd_idx_o(loop_stack_rd_idx),
    .stack_read_o  (),

    .next_top_data_o(next_loop_addr_info),
    .next_top_valid_o(next_loop_valid)
  );

  for(genvar i_count = 0; i_count < LoopStackDepth; i_count = i_count + 1) begin : g_loop_counters
    logic loop_count_set;
    logic loop_count_dec;

    assign loop_count_set = loop_stack_write & (loop_stack_wr_idx == i_count);
    assign loop_count_dec = current_loop_counter_dec & (loop_stack_rd_idx == i_count);

    //SEC_CM: LOOP_STACK.CTR.REDUN
    prim_count #(
      .Width(32),
      .ResetValue({32{1'b1}})
    ) u_loop_count (
      .clk_i,
      .rst_ni,
      .clr_i     (state_reset_i),
      .set_i     (loop_count_set),
      .set_cnt_i (new_loop.loop_iterations),
      .incr_en_i (1'b0),
      .decr_en_i (loop_count_dec), // count down
      .step_i    (32'd1),
      .cnt_o     (loop_counters[i_count]),
      .cnt_next_o(),
      .err_o     (loop_counter_err[i_count])
    );

    assign loop_counter_err_d[i_count] = loop_counter_err_q[i_count] | loop_counter_err[i_count];

    // Cannot clear and set prim_count in the same cycle
    `ASSERT(NoLoopCountClrAndSet_A, !(state_reset_i & loop_count_set))
  end

  prim_flop #(
    .Width(LoopStackDepth),
    .ResetValue('0)
  ) u_loop_counter_err_flop (
    .clk_i,
    .rst_ni,

    .d_i(loop_counter_err_d),
    .q_o(loop_counter_err_q)
  );

  assign current_loop.loop_iterations = loop_counters[loop_stack_rd_idx];

  assign current_loop_addrs_padded_intg_unbuf =
    {current_loop.loop_addr_info.loop_addrs_intg,
     {(32 - (ImemAddrWidth * 2) - 1){1'b0}},
     current_loop.loop_addr_info.loop_start,
     current_loop.loop_addr_info.loop_end};

  prim_buf #(
    .Width(39)
  ) u_current_loop_addrs_padded_intg_buf (
    .in_i (current_loop_addrs_padded_intg_unbuf),
    .out_o(current_loop_addrs_padded_intg_buf)
  );

  //SEC_CM: LOOP_STACK.ADDR.INTEGRITY
  prim_secded_inv_39_32_dec u_loop_addrs_intg_dec (
    .data_i     (current_loop_addrs_padded_intg_buf),
    .data_o     (),
    .syndrome_o (),
    .err_o      (current_loop_intg_err)
  );

  assign hw_err_o = (|loop_counter_err_d) |
                    loop_stack_cnt_err    |
                    ((|current_loop_intg_err) & current_loop_valid);

  assign predec_err_o =
    (loop_end_addr_predec_i != new_loop_end_addr_full[ImemAddrWidth-1:0]) & loop_start_req_i;

  // Forward info about loop state for next cycle to prefetch stage
  assign prefetch_loop_active_o = next_loop_valid;

  // Iterations for the current loop on the next cycle depend upon a number of factors
  // - If the loop stack is being popped the next counter on the stack provides the new iterations
  // - If the current loop iterations are being decremented new iterations are the decremented value
  // - If a new loop is starting it's iterations are the new iterations
  // - Otherwise next loop iterations is just the current loop iterations
  logic [31:0] current_loop_iterations_dec;
  logic [StackDepthW-1:0] loop_stack_rd_idx_dec;
  assign current_loop_iterations_dec = current_loop.loop_iterations - 32'd1;
  assign loop_stack_rd_idx_dec = loop_stack_rd_idx - 1'b1;
  assign prefetch_loop_iterations_o =
    loop_stack_pop           ? loop_counters[loop_stack_rd_idx_dec] :
    current_loop_counter_dec ? current_loop_iterations_dec          :
    loop_stack_write         ? new_loop.loop_iterations             :
                               current_loop.loop_iterations;

  logic unused_next_loop_addr_info_intg;
  assign unused_next_loop_addr_info_intg = ^next_loop_addr_info.loop_addrs_intg;

  assign prefetch_loop_end_addr_o  = next_loop_addr_info.loop_end;
  assign prefetch_loop_jump_addr_o = next_loop_addr_info.loop_start;

  `ASSERT(NoLoopStackPushAndPop, !(loop_stack_push && loop_stack_pop))
  `ASSERT(NoLoopWriteIfCounterDec, current_loop_counter_dec |-> !loop_stack_write)
endmodule
