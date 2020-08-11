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
    // Size of the instruction memory, in bytes
    parameter int ImemSizeByte = 4096,
    // Size of the data memory, in bytes
    parameter int DmemSizeByte = 4096,

    localparam int ImemAddrWidth = prim_util_pkg::vbits (ImemSizeByte),
    localparam int DmemAddrWidth = prim_util_pkg::vbits (DmemSizeByte)
) (
    input logic clk_i,
    input logic rst_ni,

    input  logic start_i,  // start the operation
    output logic done_o,  // operation done

    input logic [ImemAddrWidth-1:0] start_addr_i,  // start byte address in IMEM

    // Instruction memory (IMEM)
    output logic                     imem_req_o,
    output logic [ImemAddrWidth-1:0] imem_addr_o,
    output logic [             31:0] imem_wdata_o,
    input  logic [             31:0] imem_rdata_i,
    input  logic                     imem_rvalid_i,
    input  logic [              1:0] imem_rerror_i,

    // Data memory (DMEM)
    output logic                     dmem_req_o,
    output logic                     dmem_write_o,
    output logic [DmemAddrWidth-1:0] dmem_addr_o,
    output logic [         WLEN-1:0] dmem_wdata_o,
    output logic [         WLEN-1:0] dmem_wmask_o,
    input  logic [         WLEN-1:0] dmem_rdata_i,
    input  logic                     dmem_rvalid_i,
    input  logic [              1:0] dmem_rerror_i
);
  // Random number
  // TODO: Hook up to RNG distribution network
  // TODO: Decide what guarantees we make for random numbers on CSRs/WSRs, and how they might or
  // might not come from the same source.
  logic [WLEN-1:0] rnd;
  assign rnd = 'd42;

  // Fetch request (the next instruction)
  logic [ImemAddrWidth-1:0] insn_fetch_req_addr;
  logic insn_fetch_req_valid;

  // Fetch response (the current instruction before it is decoded)
  logic insn_fetch_resp_valid;
  logic [ImemAddrWidth-1:0] insn_fetch_resp_addr;
  logic [31:0] insn_fetch_resp_data;

  // The currently executed instruction.
  logic insn_valid;
  logic insn_illegal;
  logic [ImemAddrWidth-1:0] insn_addr;
  insn_dec_base_t insn_dec_base;

  insn_dec_ctrl_t insn_dec_ctrl;

  logic [4:0] rf_base_wr_addr;
  logic rf_base_wr_en;
  logic [31:0] rf_base_wr_data;
  logic [4:0] rf_base_rd_addr_a;
  logic [31:0] rf_base_rd_data_a;
  logic [4:0] rf_base_rd_addr_b;
  logic [31:0] rf_base_rd_data_b;

  alu_base_operation_t alu_base_operation;
  alu_base_comparison_t alu_base_comparison;
  logic [31:0] alu_base_operation_result;
  logic alu_base_comparison_result;

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
      .insn_fetch_req_addr_i (insn_fetch_req_addr),
      .insn_fetch_req_valid_i(insn_fetch_req_valid),

      // Fetched instruction
      .insn_fetch_resp_addr_o (insn_fetch_resp_addr),
      .insn_fetch_resp_valid_o(insn_fetch_resp_valid),
      .insn_fetch_resp_data_o (insn_fetch_resp_data)
  );

  assign imem_wdata_o = '0;

  // Instruction decoder
  otbn_decoder u_otbn_decoder (
      // The decoder is combinatorial; clk and rst are only used for assertions.
      .clk_i,
      .rst_ni,

      // Instruction to decode
      .insn_fetch_resp_data_i (insn_fetch_resp_data),
      .insn_fetch_resp_valid_i(insn_fetch_resp_valid),

      // Decoded instruction
      .insn_valid_o   (insn_valid),
      .insn_illegal_o (insn_illegal),
      .insn_dec_base_o(insn_dec_base),
      .insn_dec_ctrl_o(insn_dec_ctrl)
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
      .start_addr_i,

      // Next instruction selection (to instruction fetch)
      .insn_fetch_req_addr_o (insn_fetch_req_addr),
      .insn_fetch_req_valid_o(insn_fetch_req_valid),

      // The current instruction
      .insn_valid_i(insn_valid),
      .insn_addr_i (insn_addr),

      // Decoded instruction from decoder
      .insn_dec_base_i(insn_dec_base),
      .insn_dec_ctrl_i(insn_dec_ctrl),

      // To/from base register file
      .rf_base_wr_addr_o  (rf_base_wr_addr),
      .rf_base_wr_en_o    (rf_base_wr_en),
      .rf_base_wr_data_o  (rf_base_wr_data),
      .rf_base_rd_addr_a_o(rf_base_rd_addr_a),
      .rf_base_rd_data_a_i(rf_base_rd_data_a),
      .rf_base_rd_addr_b_o(rf_base_rd_addr_b),
      .rf_base_rd_data_b_i(rf_base_rd_data_b),

      // To/from base ALU
      .alu_base_operation_o        (alu_base_operation),
      .alu_base_comparison_o       (alu_base_comparison),
      .alu_base_operation_result_i (alu_base_operation_result),
      .alu_base_comparison_result_i(alu_base_comparison_result)
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
      .dmem_rerror_i

      // Data from base and bn execute blocks.
      // TODO: Add signals to controller
  );

  // Control and Status registers
  // 32b Control and Status Registers (CSRs), and WLEN Wide Special-Purpose Registers (WSRs)
  otbn_status_registers u_otbn_status_registers (
      .clk_i,
      .rst_ni,
      .rnd_i(rnd)

      // TODO: Add CSR and WSR read/write ports to controller.

      // TODO: Add potential side-channel signals.
  );

  // Base Instruction Subset =======================================================================

  // General-Purpose Register File (GPRs): 32 32b registers
  otbn_rf_base u_otbn_rf_base (
      .clk_i,
      .rst_ni,

      .wr_addr_i(rf_base_wr_addr),
      .wr_en_i  (rf_base_wr_en),
      .wr_data_i(rf_base_wr_data),

      .rd_addr_a_i(rf_base_rd_addr_a),
      .rd_data_a_o(rf_base_rd_data_a),
      .rd_addr_b_i(rf_base_rd_addr_b),
      .rd_data_b_o(rf_base_rd_data_b)
  );

  otbn_alu_base u_otbn_alu_base (
      .clk_i,
      .rst_ni,

      .operation_i        (alu_base_operation),
      .comparison_i       (alu_base_comparison),
      .operation_result_o (alu_base_operation_result),
      .comparison_result_o(alu_base_comparison_result)
  );
endmodule
