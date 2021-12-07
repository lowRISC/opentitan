// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Instruction Fetch Unit
 *
 * Fetch an instruction from the instruction memory.
 */
module otbn_instruction_fetch
  import otbn_pkg::*;
#(
  parameter int ImemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,

  // Instruction memory (IMEM) interface. Read-only.
  output logic                     imem_req_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  input  logic [38:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,

  // Next instruction selection (to instruction fetch)
  input  logic                     insn_fetch_req_valid_i,
  input  logic [ImemAddrWidth-1:0] insn_fetch_req_addr_i,

  // Decoded instruction
  output logic                     insn_fetch_resp_valid_o,
  output logic [ImemAddrWidth-1:0] insn_fetch_resp_addr_o,
  output logic [31:0]              insn_fetch_resp_data_o,
  input  logic                     insn_fetch_resp_clear_i,

  output logic                     insn_fetch_err_o, // ECC error seen in instruction fetch

  input logic                     prefetch_en_i,
  input logic                     prefetch_loop_active_i,
  input logic [31:0]              prefetch_loop_iterations_i,
  input logic [ImemAddrWidth-1:0] prefetch_loop_end_addr_i,
  input logic [ImemAddrWidth-1:0] prefetch_loop_jump_addr_i
);

  function automatic logic insn_is_branch(logic [31:0] insn_data);
    logic [31:7] unused_insn_data;

    unused_insn_data = insn_data[31:7];

    return insn_data[6:0] inside {InsnOpcodeBaseBranch, InsnOpcodeBaseJal, InsnOpcodeBaseJalr};
  endfunction

  logic [ImemAddrWidth-1:0] insn_prefetch_addr;
  logic [38:0]              insn_fetch_resp_data_intg_q;
  logic [ImemAddrWidth-1:0] insn_fetch_resp_addr_q;
  logic                     insn_fetch_resp_valid_q, insn_fetch_resp_valid_d;
  logic [1:0]               insn_fetch_resp_intg_error_vec;
  logic                     insn_fetch_en;

  logic                     insn_prefetch;
  logic                     insn_prefetch_fail;

  // The prefetch has failed if a fetch is requested and either no prefetch has done or was done to
  // the wrong address.
  assign insn_prefetch_fail = insn_fetch_req_valid_i &
                              (~imem_rvalid_i || (insn_fetch_req_addr_i != insn_prefetch_addr));

  // Fetch response is valid when prefetch has matched what was requested. Otherwise if no fetch is
  // requested keep fetch response validity constant unless a clear is commanded.
  assign insn_fetch_resp_valid_d =
    insn_fetch_req_valid_i ? imem_rvalid_i & (insn_fetch_req_addr_i == insn_prefetch_addr) :
                             insn_fetch_resp_valid_q & ~insn_fetch_resp_clear_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      insn_fetch_resp_valid_q <= 1'b0;
    end else begin
      insn_fetch_resp_valid_q <= insn_fetch_resp_valid_d;
    end
  end

  assign insn_fetch_en = imem_rvalid_i & insn_fetch_req_valid_i;

  always_ff @(posedge clk_i) begin
    if (insn_fetch_en) begin
      insn_fetch_resp_data_intg_q <= imem_rdata_i;
      insn_fetch_resp_addr_q      <= insn_prefetch_addr;
    end
  end

  always_ff @(posedge clk_i) begin
    if (insn_prefetch) begin
      insn_prefetch_addr <= imem_addr_o;
    end
  end

  // Prefetch control
  always_comb begin
    // Only prefetch if controller tells us to
    insn_prefetch = prefetch_en_i;
    // By default prefetch the next instruction
    imem_addr_o = insn_prefetch_addr + 'd4;

    if (!insn_fetch_req_valid_i) begin
      // Keep prefetching the same instruction when a new one isn't being requested. In this
      // scenario OTBN is stalled and will eventually want the prefetched instruction.
      imem_addr_o = insn_prefetch_addr;
    end else if (insn_prefetch_fail) begin
      // When prefetching has failed prefetch the requested address
      imem_addr_o = insn_fetch_req_addr_i;
    end else if (insn_is_branch(imem_rdata_i[31:0])) begin
      // For a branch we do not know if it will be taken or untaken. So never prefetch to keep
      // timing consistent regardless of taken/not-taken.
      // This also applies to jumps, this avoids the need to calculate the jump address here.
      insn_prefetch = 1'b0;
    end else if (insn_prefetch_addr == prefetch_loop_end_addr_i && prefetch_loop_active_i &&
                 prefetch_loop_iterations_i > 32'd1) begin
      // When in a loop prefetch the loop beginning when execution reaches the end.
      imem_addr_o = prefetch_loop_jump_addr_i;
    end
  end

  // Check integrity on prefetched instruction
  prim_secded_inv_39_32_dec u_insn_intg_check (
    .data_i     (insn_fetch_resp_data_intg_q),
    .data_o     (),
    .syndrome_o (),
    .err_o      (insn_fetch_resp_intg_error_vec)
  );

  assign imem_req_o = insn_prefetch;

  assign insn_fetch_resp_valid_o = insn_fetch_resp_valid_q;
  assign insn_fetch_resp_addr_o  = insn_fetch_resp_addr_q;
  // Strip integrity bits before passing instruction to decoder
  assign insn_fetch_resp_data_o  = insn_fetch_resp_data_intg_q[31:0];

  assign insn_fetch_err_o = |insn_fetch_resp_intg_error_vec & insn_fetch_resp_valid_q;

  // We should always get prefetches correct, the check exists as an integrity check only
  `ASSERT(NoAddressMismatch,
          imem_rvalid_i && insn_fetch_req_valid_i |-> insn_fetch_req_addr_i == insn_prefetch_addr)
  `ASSERT(FetchEnOnlyIfValidIMem, insn_fetch_en |-> imem_rvalid_i)
endmodule
