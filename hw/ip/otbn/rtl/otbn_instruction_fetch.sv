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
  input logic                     insn_fetch_req_valid_i,
  input logic                     insn_fetch_req_valid_raw_i,
  input logic [ImemAddrWidth-1:0] insn_fetch_req_addr_i,

  // Decoded instruction
  output logic                     insn_fetch_resp_valid_o,
  output logic [ImemAddrWidth-1:0] insn_fetch_resp_addr_o,
  output logic [31:0]              insn_fetch_resp_data_o,
  input  logic                     insn_fetch_resp_clear_i,

  output rf_predec_bignum_t   rf_predec_bignum_o,
  output alu_predec_bignum_t  alu_predec_bignum_o,
  output ispr_predec_bignum_t ispr_predec_bignum_o,
  output mac_predec_bignum_t  mac_predec_bignum_o,
  output logic                lsu_addr_en_predec_o,

  input logic [NWdr-1:0] rf_bignum_rd_a_indirect_onehot_i,
  input logic [NWdr-1:0] rf_bignum_rd_b_indirect_onehot_i,
  input logic [NWdr-1:0] rf_bignum_wr_indirect_onehot_i,
  input logic            rf_bignum_indirect_en_i,

  output logic insn_fetch_err_o,  // ECC error seen in instruction fetch
  output logic insn_addr_err_o,

  input logic                     prefetch_en_i,
  input logic                     prefetch_loop_active_i,
  input logic [31:0]              prefetch_loop_iterations_i,
  input logic [ImemAddrWidth:0]   prefetch_loop_end_addr_i,
  input logic [ImemAddrWidth-1:0] prefetch_loop_jump_addr_i,
  input logic                     prefetch_ignore_errs_i,

  input logic                     sec_wipe_wdr_en_i,
  input logic [4:0]               sec_wipe_wdr_addr_i
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

  rf_predec_bignum_t   rf_predec_bignum_indirect, rf_predec_bignum_sec_wipe;
  rf_predec_bignum_t   rf_predec_bignum_q, rf_predec_bignum_d, rf_predec_bignum_insn;
  alu_predec_bignum_t  alu_predec_bignum_q, alu_predec_bignum_d;
  ispr_predec_bignum_t ispr_predec_bignum_q, ispr_predec_bignum_d;
  ispr_predec_bignum_t ispr_predec_bignum;
  mac_predec_bignum_t  mac_predec_bignum_q, mac_predec_bignum_d;
  logic                lsu_addr_en_predec_q, lsu_addr_en_predec_d;
  logic                lsu_addr_en_predec_insn;
  logic                insn_addr_err_unbuf;

  logic [NWdr-1:0] rf_bignum_wr_sec_wipe_onehot;

  logic rf_predec_bignum_en, other_predec_en;

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

  // SEC_CM: DATA_REG_SW.SCA
  otbn_predecode u_otbn_predecode (
    .clk_i,
    .rst_ni,

    .imem_rdata_i (imem_rdata_i[31:0]),
    .imem_rvalid_i,

    .rf_predec_bignum_o   (rf_predec_bignum_insn),
    .alu_predec_bignum_o  (alu_predec_bignum_d),
    .ispr_predec_bignum_o (ispr_predec_bignum),
    .mac_predec_bignum_o  (mac_predec_bignum_d),
    .lsu_addr_en_predec_o (lsu_addr_en_predec_insn)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_we_bignum_sec_wipe_onehot_enc (
    .in_i  (sec_wipe_wdr_addr_i),
    .en_i  (sec_wipe_wdr_en_i),
    .out_o (rf_bignum_wr_sec_wipe_onehot)
  );

  // Indirect register addressing
  // For instructions using indirect addressing (BN.LID/BN.SID/BN.MOVR) the base register read to
  // determine which bignum register is used occurs in the first cycle of the instruction
  // execution. The onehot encoded version of the register index is passed back here (via the
  // `rf_bignum_*_indirect_onehot_i` signals to set the enables for the following cycle.
  assign rf_predec_bignum_indirect = '{rf_ren_a : rf_bignum_rd_a_indirect_onehot_i,
                                       rf_ren_b : rf_bignum_rd_b_indirect_onehot_i,
                                       rf_we    : rf_bignum_wr_indirect_onehot_i};

  assign rf_predec_bignum_sec_wipe = '{rf_ren_a : '0,
                                            rf_ren_b : '0,
                                            rf_we    : rf_bignum_wr_sec_wipe_onehot};

  // Register enables for bignum come from precode unless indirect register accesses are used
  assign rf_predec_bignum_d = sec_wipe_wdr_en_i       ? rf_predec_bignum_sec_wipe :
                              rf_bignum_indirect_en_i ? rf_predec_bignum_indirect :
                              insn_fetch_en           ? rf_predec_bignum_insn     :
                                                        '0;

  assign rf_predec_bignum_en =
    insn_fetch_en | rf_bignum_indirect_en_i | sec_wipe_wdr_en_i | insn_fetch_resp_clear_i;

  assign ispr_predec_bignum_d = insn_fetch_en ? ispr_predec_bignum : '0;

  assign lsu_addr_en_predec_d = lsu_addr_en_predec_insn & insn_fetch_en;

  assign other_predec_en = insn_fetch_en | insn_fetch_resp_clear_i;

  assign insn_fetch_en = imem_rvalid_i & insn_fetch_req_valid_i;

  always_ff @(posedge clk_i) begin
    if (insn_fetch_en) begin
      insn_fetch_resp_data_intg_q <= imem_rdata_i;
      insn_fetch_resp_addr_q      <= insn_prefetch_addr;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      alu_predec_bignum_q <= '0;
      mac_predec_bignum_q <= '0;
    end else if (insn_fetch_en) begin
      alu_predec_bignum_q <= alu_predec_bignum_d;
      mac_predec_bignum_q <= mac_predec_bignum_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rf_predec_bignum_q <= '0;
    end else if (rf_predec_bignum_en) begin
      rf_predec_bignum_q <= rf_predec_bignum_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ispr_predec_bignum_q <= '0;
      lsu_addr_en_predec_q <= 1'b0;
    end else if (other_predec_en) begin
      ispr_predec_bignum_q <= ispr_predec_bignum_d;
      lsu_addr_en_predec_q <= lsu_addr_en_predec_d;
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
    end else if ({1'b0, insn_prefetch_addr} == prefetch_loop_end_addr_i &&
                 prefetch_loop_active_i &&
                 prefetch_loop_iterations_i > 32'd1) begin
      // When in a loop prefetch the loop beginning when execution reaches the end.
      imem_addr_o = prefetch_loop_jump_addr_i;
    end
  end

  // SEC_CM: INSTRUCTION.MEM.INTEGRITY
  // Check integrity on prefetched instruction
  prim_secded_inv_39_32_dec u_insn_intg_check (
    .data_i    (insn_fetch_resp_data_intg_q),
    .data_o    (),
    .syndrome_o(),
    .err_o     (insn_fetch_resp_intg_error_vec)
  );


  assign imem_req_o = insn_prefetch;

  assign insn_fetch_resp_valid_o = insn_fetch_resp_valid_q;
  assign insn_fetch_resp_addr_o  = insn_fetch_resp_addr_q;
  // Strip integrity bits before passing instruction to decoder
  assign insn_fetch_resp_data_o  = insn_fetch_resp_data_intg_q[31:0];

  assign insn_fetch_err_o = |insn_fetch_resp_intg_error_vec & insn_fetch_resp_valid_q;

  // SEC_CM: PC.CTRL_FLOW.REDUN
  // Signal an `insn_addr_err` if the instruction the execute stage requests is not the one that was
  // prefetched. By design the prefetcher is either correct or doesn't prefetch, so a mismatch
  // here indicates a fault.  `insn_fetch_req_valid_raw_i` is used as it doesn't factor in errors,
  // which is required here otherwise we get a combinational loop.
  assign insn_addr_err_unbuf =
    imem_rvalid_i & insn_fetch_req_valid_raw_i & ~prefetch_ignore_errs_i &
    (insn_fetch_req_addr_i != insn_prefetch_addr);

  prim_buf #(.Width(1)) u_insn_addr_buf (
    .in_i(insn_addr_err_unbuf),
    .out_o(insn_addr_err_o)
  );

  assign rf_predec_bignum_o   = rf_predec_bignum_q;
  assign alu_predec_bignum_o  = alu_predec_bignum_q;
  assign ispr_predec_bignum_o = ispr_predec_bignum_q;
  assign mac_predec_bignum_o  = mac_predec_bignum_q;
  assign lsu_addr_en_predec_o = lsu_addr_en_predec_q;

  `ASSERT(FetchEnOnlyIfValidIMem, insn_fetch_en |-> imem_rvalid_i)
  `ASSERT(NoFetchEnAndIndirectEn, !(insn_fetch_en && rf_bignum_indirect_en_i))
endmodule
