// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * OTBN Instruction Prefetch Controller
 *
 * Determine if and from which address an instruction should be prefetched.
 */
module otbn_instruction_prefetch_controller #(
  parameter int AddrWidth = 0,
  parameter bit BufOutput = 1'b0
) (
  input  logic                  prefetch_en_i,
  input  logic [AddrWidth-1:0]  insn_prefetch_addr_i,
  input  logic                  insn_prefetch_fail_i,
  input  logic [AddrWidth-1:0]  insn_fetch_req_addr_i,
  input  logic                  insn_fetch_req_valid_i,
  input  logic [6:0]            imem_rdata_lsb_i,
  input  logic                  prefetch_loop_active_i,
  input  logic                  insn_prefetch_addr_is_loop_end_addr_i,
  input  logic [AddrWidth-1:0]  prefetch_loop_jump_addr_i,
  input  logic                  prefetch_loop_iterations_gt_one_i,

  output logic                  insn_prefetch_o,
  output logic [AddrWidth-1:0]  imem_addr_o

);
  function automatic logic opcode_is_branch(logic [6:0] opcode);
    import otbn_pkg::*;
    return opcode inside {InsnOpcodeBaseBranch, InsnOpcodeBaseJal, InsnOpcodeBaseJalr};
  endfunction

  logic                 insn_prefetch;
  logic [AddrWidth-1:0] imem_addr;
  always_comb begin
    // Only prefetch if controller tells us to
    insn_prefetch = prefetch_en_i;
    // By default prefetch the next instruction
    imem_addr = insn_prefetch_addr_i + 'd4;

    if (!insn_fetch_req_valid_i) begin
      // Keep prefetching the same instruction when a new one isn't being requested. In this
      // scenario OTBN is stalled and will eventually want the prefetched instruction.
      imem_addr = insn_prefetch_addr_i;
    end else if (insn_prefetch_fail_i) begin
      // When prefetching has failed prefetch the requested address
      imem_addr = insn_fetch_req_addr_i;
    end else if (opcode_is_branch(imem_rdata_lsb_i)) begin
      // For a branch we do not know if it will be taken or untaken. So never prefetch to keep
      // timing consistent regardless of taken/not-taken.
      // This also applies to jumps, this avoids the need to calculate the jump address here.
      insn_prefetch = 1'b0;
    end else if (insn_prefetch_addr_is_loop_end_addr_i &&
                 prefetch_loop_active_i &&
                 prefetch_loop_iterations_gt_one_i) begin
      // When in a loop prefetch the loop beginning when execution reaches the end.
      imem_addr = prefetch_loop_jump_addr_i;
    end
  end

  if (BufOutput) begin : g_oup_buf
    // Buffer outputs to make sure glitches don't back-propagate to inputs.
    prim_buf #(
      .Width(1)
    ) u_insn_prefetch_buf (
      .in_i   (insn_prefetch),
      .out_o  (insn_prefetch_o)
    );
    prim_buf #(
      .Width(AddrWidth)
    ) u_imem_addr_buf (
      .in_i   (imem_addr),
      .out_o  (imem_addr_o)
    );
  end else begin : g_no_oup_buf
    assign insn_prefetch_o = insn_prefetch;
    assign imem_addr_o = imem_addr;
  end

endmodule
