// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */
module otbn_core
  import otbn_pkg::*;
#(
  // Register file implementation selection, see otbn_pkg.sv.
  parameter regfile_e RegFile = RegFileFF,

  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
)(
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  start_i, // start the operation
  output logic  done_o,  // operation done

  output err_bits_t err_bits_o, // valid when done_o is asserted

  input  logic [ImemAddrWidth-1:0] start_addr_i, // start byte address in IMEM

  // Instruction memory (IMEM)
  output logic                     imem_req_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  output logic [31:0]              imem_wdata_o,
  input  logic [31:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,
  input  logic                     imem_rerror_i,

  // Data memory (DMEM)
  output logic                     dmem_req_o,
  output logic                     dmem_write_o,
  output logic [DmemAddrWidth-1:0] dmem_addr_o,
  output logic [WLEN-1:0]          dmem_wdata_o,
  output logic [WLEN-1:0]          dmem_wmask_o,
  input  logic [WLEN-1:0]          dmem_rdata_i,
  input  logic                     dmem_rvalid_i,
  input  logic                     dmem_rerror_i
);
  // Random number
  // TODO: Hook up to RNG distribution network
  // TODO: Decide what guarantees we make for random numbers on CSRs/WSRs, and how they might or
  // might not come from the same source.
  logic [WLEN-1:0] rnd;

  // Constant for now until RNG is set up. This constant is the same in the model and must be
  // altered there to match is altered here (the `_random_value` variable in the `RandWSR` class in
  // dv/otbn/sim/wsr.py).
  assign rnd = 256'h9999999999999999999999999999999999999999999999999999999999999999;

  // Fetch request (the next instruction)
  logic [ImemAddrWidth-1:0] insn_fetch_req_addr;
  logic                     insn_fetch_req_valid;

  // Fetch response (the current instruction before it is decoded)
  logic                     insn_fetch_resp_valid;
  logic [ImemAddrWidth-1:0] insn_fetch_resp_addr;
  logic [31:0]              insn_fetch_resp_data;
  logic                     insn_fetch_err;

  // The currently executed instruction.
  logic                     insn_valid;
  logic                     insn_illegal;
  logic [ImemAddrWidth-1:0] insn_addr;
  insn_dec_base_t           insn_dec_base;
  insn_dec_bignum_t         insn_dec_bignum;
  insn_dec_shared_t         insn_dec_shared;

  logic [4:0]   rf_base_wr_addr;
  logic         rf_base_wr_en;
  logic [31:0]  rf_base_wr_data;
  logic [4:0]   rf_base_rd_addr_a;
  logic         rf_base_rd_en_a;
  logic [31:0]  rf_base_rd_data_a;
  logic [4:0]   rf_base_rd_addr_b;
  logic         rf_base_rd_en_b;
  logic [31:0]  rf_base_rd_data_b;
  logic         rf_base_rd_commit;
  logic         rf_base_call_stack_err;

  alu_base_operation_t  alu_base_operation;
  alu_base_comparison_t alu_base_comparison;
  logic [31:0]          alu_base_operation_result;
  logic                 alu_base_comparison_result;

  logic                     lsu_load_req;
  logic                     lsu_store_req;
  insn_subset_e             lsu_req_subset;
  logic [DmemAddrWidth-1:0] lsu_addr;

  logic [31:0]              lsu_base_wdata;
  logic [WLEN-1:0]          lsu_bignum_wdata;

  logic [31:0]              lsu_base_rdata;
  logic [WLEN-1:0]          lsu_bignum_rdata;
  logic                     lsu_rdata_err;

  logic [WdrAw-1:0] rf_bignum_wr_addr;
  logic [1:0]       rf_bignum_wr_en;
  logic [WLEN-1:0]  rf_bignum_wr_data;
  logic [WdrAw-1:0] rf_bignum_rd_addr_a;
  logic [WLEN-1:0]  rf_bignum_rd_data_a;
  logic [WdrAw-1:0] rf_bignum_rd_addr_b;
  logic [WLEN-1:0]  rf_bignum_rd_data_b;

  alu_bignum_operation_t alu_bignum_operation;
  logic [WLEN-1:0]       alu_bignum_operation_result;

  mac_bignum_operation_t mac_bignum_operation;
  logic [WLEN-1:0]       mac_bignum_operation_result;
  flags_t                mac_bignum_operation_flags;
  flags_t                mac_bignum_operation_flags_en;
  logic                  mac_bignum_en;

  ispr_e                       ispr_addr;
  logic [31:0]                 ispr_base_wdata;
  logic [BaseWordsPerWLEN-1:0] ispr_base_wr_en;
  logic [WLEN-1:0]             ispr_bignum_wdata;
  logic                        ispr_bignum_wr_en;
  logic [WLEN-1:0]             ispr_rdata;
  logic [WLEN-1:0]             ispr_acc;
  logic [WLEN-1:0]             ispr_acc_wr_data;
  logic                        ispr_acc_wr_en;

  // Depending on its usage, the instruction address (program counter) is qualified by two valid
  // signals: insn_fetch_resp_valid (together with the undecoded instruction data), and insn_valid
  // for valid decoded (i.e. legal) instructions. Duplicate the signal in the source code for
  // consistent grouping of signals with their valid signal.
  assign insn_addr = insn_fetch_resp_addr;

  // Instruction fetch unit
  otbn_instruction_fetch #(
    .ImemSizeByte(ImemSizeByte)
  ) u_otbn_instruction_fetch (
    .clk_i,
    .rst_ni,

    // Instruction memory interface
    .imem_req_o,
    .imem_addr_o,
    .imem_rdata_i,
    .imem_rvalid_i,
    .imem_rerror_i,

    // Instruction to fetch
    .insn_fetch_req_addr_i  (insn_fetch_req_addr),
    .insn_fetch_req_valid_i (insn_fetch_req_valid),

    // Fetched instruction
    .insn_fetch_resp_addr_o  (insn_fetch_resp_addr),
    .insn_fetch_resp_valid_o (insn_fetch_resp_valid),
    .insn_fetch_resp_data_o  (insn_fetch_resp_data),
    .insn_fetch_err_o        (insn_fetch_err)
  );

  assign imem_wdata_o = '0;

  // Instruction decoder
  otbn_decoder u_otbn_decoder (
    // The decoder is combinatorial; clk and rst are only used for assertions.
    .clk_i,
    .rst_ni,

    // Instruction to decode
    .insn_fetch_resp_data_i  (insn_fetch_resp_data),
    .insn_fetch_resp_valid_i (insn_fetch_resp_valid),

    // Decoded instruction
    .insn_valid_o      (insn_valid),
    .insn_illegal_o    (insn_illegal),
    .insn_dec_base_o   (insn_dec_base),
    .insn_dec_bignum_o (insn_dec_bignum),
    .insn_dec_shared_o (insn_dec_shared)
  );

  // Controller: coordinate between functional units, prepare their inputs (e.g. by muxing between
  // operand sources), and post-process their outputs as needed.
  otbn_controller #(
    .ImemSizeByte(ImemSizeByte),
    .DmemSizeByte(DmemSizeByte)
  ) u_otbn_controller (
    .clk_i,
    .rst_ni,

    .start_i,
    .done_o,

    .err_bits_o,

    .start_addr_i,

    // Next instruction selection (to instruction fetch)
    .insn_fetch_req_addr_o  (insn_fetch_req_addr),
    .insn_fetch_req_valid_o (insn_fetch_req_valid),
    // Error from fetch requested last cycle
    .insn_fetch_err_i       (insn_fetch_err),

    // The current instruction
    .insn_valid_i   (insn_valid),
    .insn_illegal_i (insn_illegal),
    .insn_addr_i    (insn_addr),

    // Decoded instruction from decoder
    .insn_dec_base_i   (insn_dec_base),
    .insn_dec_bignum_i (insn_dec_bignum),
    .insn_dec_shared_i (insn_dec_shared),

    // To/from base register file
    .rf_base_wr_addr_o        (rf_base_wr_addr),
    .rf_base_wr_en_o          (rf_base_wr_en),
    .rf_base_wr_data_o        (rf_base_wr_data),
    .rf_base_rd_addr_a_o      (rf_base_rd_addr_a),
    .rf_base_rd_en_a_o        (rf_base_rd_en_a),
    .rf_base_rd_data_a_i      (rf_base_rd_data_a),
    .rf_base_rd_addr_b_o      (rf_base_rd_addr_b),
    .rf_base_rd_en_b_o        (rf_base_rd_en_b),
    .rf_base_rd_data_b_i      (rf_base_rd_data_b),
    .rf_base_rd_commit_o      (rf_base_rd_commit),
    .rf_base_call_stack_err_i (rf_base_call_stack_err),

    // To/from bignunm register file
    .rf_bignum_wr_addr_o   (rf_bignum_wr_addr),
    .rf_bignum_wr_en_o     (rf_bignum_wr_en),
    .rf_bignum_wr_data_o   (rf_bignum_wr_data),
    .rf_bignum_rd_addr_a_o (rf_bignum_rd_addr_a),
    .rf_bignum_rd_data_a_i (rf_bignum_rd_data_a),
    .rf_bignum_rd_addr_b_o (rf_bignum_rd_addr_b),
    .rf_bignum_rd_data_b_i (rf_bignum_rd_data_b),

    // To/from base ALU
    .alu_base_operation_o         (alu_base_operation),
    .alu_base_comparison_o        (alu_base_comparison),
    .alu_base_operation_result_i  (alu_base_operation_result),
    .alu_base_comparison_result_i (alu_base_comparison_result),

    // To/from bignum ALU
    .alu_bignum_operation_o         (alu_bignum_operation),
    .alu_bignum_operation_result_i  (alu_bignum_operation_result),

    // To/from bignum MAC
    .mac_bignum_operation_o        (mac_bignum_operation),
    .mac_bignum_operation_result_i (mac_bignum_operation_result),
    .mac_bignum_en_o               (mac_bignum_en),

    // To/from LSU (base and bignum)
    .lsu_load_req_o     (lsu_load_req),
    .lsu_store_req_o    (lsu_store_req),
    .lsu_req_subset_o   (lsu_req_subset),
    .lsu_addr_o         (lsu_addr),

    .lsu_base_wdata_o   (lsu_base_wdata),
    .lsu_bignum_wdata_o (lsu_bignum_wdata),

    .lsu_base_rdata_i   (lsu_base_rdata),
    .lsu_bignum_rdata_i (lsu_bignum_rdata),
    .lsu_rdata_err_i    (lsu_rdata_err),

    // Isprs read/write (base and bignum)
    .ispr_addr_o         (ispr_addr),
    .ispr_base_wdata_o   (ispr_base_wdata),
    .ispr_base_wr_en_o   (ispr_base_wr_en),
    .ispr_bignum_wdata_o (ispr_bignum_wdata),
    .ispr_bignum_wr_en_o (ispr_bignum_wr_en),
    .ispr_rdata_i        (ispr_rdata)
  );

  // Load store unit: read and write data from data memory
  otbn_lsu u_otbn_lsu (
    .clk_i,
    .rst_ni,

    // Data memory interface
    .dmem_req_o,
    .dmem_write_o,
    .dmem_addr_o,
    .dmem_wdata_o,
    .dmem_wmask_o,
    .dmem_rdata_i,
    .dmem_rvalid_i,
    .dmem_rerror_i,

    .lsu_load_req_i     (lsu_load_req),
    .lsu_store_req_i    (lsu_store_req),
    .lsu_req_subset_i   (lsu_req_subset),
    .lsu_addr_i         (lsu_addr),

    .lsu_base_wdata_i   (lsu_base_wdata),
    .lsu_bignum_wdata_i (lsu_bignum_wdata),

    .lsu_base_rdata_o   (lsu_base_rdata),
    .lsu_bignum_rdata_o (lsu_bignum_rdata),
    .lsu_rdata_err_o    (lsu_rdata_err)
  );

  // Base Instruction Subset =======================================================================

  otbn_rf_base #(
    .RegFile (RegFile)
  ) u_otbn_rf_base (
    .clk_i,
    .rst_ni,

    .wr_addr_i (rf_base_wr_addr),
    .wr_en_i   (rf_base_wr_en),
    .wr_data_i (rf_base_wr_data),

    .rd_addr_a_i (rf_base_rd_addr_a),
    .rd_en_a_i   (rf_base_rd_en_a),
    .rd_data_a_o (rf_base_rd_data_a),
    .rd_addr_b_i (rf_base_rd_addr_b),
    .rd_en_b_i   (rf_base_rd_en_b),
    .rd_data_b_o (rf_base_rd_data_b),
    .rd_commit_i (rf_base_rd_commit),

    .call_stack_err_o (rf_base_call_stack_err)
  );

  otbn_alu_base u_otbn_alu_base (
    .clk_i,
    .rst_ni,

    .operation_i         (alu_base_operation),
    .comparison_i        (alu_base_comparison),
    .operation_result_o  (alu_base_operation_result),
    .comparison_result_o (alu_base_comparison_result)
  );

  if (RegFile == RegFileFF) begin : gen_rf_bignum_ff
    otbn_rf_bignum_ff u_otbn_rf_bignum (
      .clk_i,
      .rst_ni,

      .wr_addr_i (rf_bignum_wr_addr),
      .wr_en_i   (rf_bignum_wr_en),
      .wr_data_i (rf_bignum_wr_data),

      .rd_addr_a_i (rf_bignum_rd_addr_a),
      .rd_data_a_o (rf_bignum_rd_data_a),
      .rd_addr_b_i (rf_bignum_rd_addr_b),
      .rd_data_b_o (rf_bignum_rd_data_b)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_rf_bignum_fpga
    otbn_rf_bignum_fpga u_otbn_rf_bignum (
      .clk_i,
      .rst_ni,

      .wr_addr_i (rf_bignum_wr_addr),
      .wr_en_i   (rf_bignum_wr_en),
      .wr_data_i (rf_bignum_wr_data),

      .rd_addr_a_i (rf_bignum_rd_addr_a),
      .rd_data_a_o (rf_bignum_rd_data_a),
      .rd_addr_b_i (rf_bignum_rd_addr_b),
      .rd_data_b_o (rf_bignum_rd_data_b)
    );
  end

  otbn_alu_bignum u_otbn_alu_bignum (
    .clk_i,
    .rst_ni,

    .operation_i              (alu_bignum_operation),
    .operation_result_o       (alu_bignum_operation_result),

    .ispr_addr_i              (ispr_addr),
    .ispr_base_wdata_i        (ispr_base_wdata),
    .ispr_base_wr_en_i        (ispr_base_wr_en),
    .ispr_bignum_wdata_i      (ispr_bignum_wdata),
    .ispr_bignum_wr_en_i      (ispr_bignum_wr_en),
    .ispr_rdata_o             (ispr_rdata),

    .ispr_acc_i               (ispr_acc),
    .ispr_acc_wr_data_o       (ispr_acc_wr_data),
    .ispr_acc_wr_en_o         (ispr_acc_wr_en),

    .mac_operation_flags_i    (mac_bignum_operation_flags),
    .mac_operation_flags_en_i (mac_bignum_operation_flags_en),

    .rnd_i                    (rnd)
  );

  otbn_mac_bignum u_otbn_mac_bignum (
    .clk_i,
    .rst_ni,

    .operation_i          (mac_bignum_operation),
    .operation_result_o   (mac_bignum_operation_result),
    .operation_flags_o    (mac_bignum_operation_flags),
    .operation_flags_en_o (mac_bignum_operation_flags_en),

    .mac_en_i           (mac_bignum_en),

    .ispr_acc_o         (ispr_acc),
    .ispr_acc_wr_data_i (ispr_acc_wr_data),
    .ispr_acc_wr_en_i   (ispr_acc_wr_en)
  );
endmodule
