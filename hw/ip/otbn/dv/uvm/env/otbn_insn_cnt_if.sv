// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Used to track instruction counts

`include "prim_assert.sv"

interface otbn_insn_cnt_if (
  input              clk_i,
  input              rst_ni,

  input logic [31:0] insn_cnt_i,
  input logic        insn_executing_i,
  input logic        stall_i,

  input bit [31:0]   model_insn_cnt_i
);

  // Check that the model and OTBN have matching instruction counters
  `ASSERT(InsnCntMatches_A, model_insn_cnt_i == insn_cnt_i)

  // As well as exposing the count itself, we've also exposed the "increment me" signal
  // (insn_executing_i && !stall_i). This means we can see when an instruction counter of all ones
  // would have incremented but saturated instead. Make sure we've exposed it properly by asserting
  // that the count works as we expect the rest of the time.
  logic [31:0] insn_cnt_r;
  logic        increment_me_r;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      insn_cnt_r     <= 0;
      increment_me_r <= 1'b0;
    end else begin
      insn_cnt_r     <= insn_cnt_i;
      increment_me_r <= insn_executing_i & ~stall_i;
    end
  end
  `ASSERT(IncWhenTold_A,
          (increment_me_r && (insn_cnt_r < '1)) |-> (insn_cnt_i == insn_cnt_r + 32'd1))

  // Now we know that the insn_executing_i and stall_i signals have the behaviour we expect, check
  // for insn_cnt saturating by expecting to see a cycle where increment_me_r is true but insn_cnt_r
  // and insn_cnt both equal '1.
  `COVER(InsnCntSaturated_C,
         increment_me_r && (insn_cnt_i == '1) && (insn_cnt_r == '1))

endinterface
