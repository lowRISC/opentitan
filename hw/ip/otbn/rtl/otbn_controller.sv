// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Controller
 */
module otbn_controller
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

    input  logic                     start_i,  // start the processing at start_addr_i
    output logic                     done_o,  // processing done, signaled by ECALL
    input  logic [ImemAddrWidth-1:0] start_addr_i,

    // Next instruction selection (to instruction fetch)
    output logic                     insn_fetch_req_valid_o,
    output logic [ImemAddrWidth-1:0] insn_fetch_req_addr_o,

    // Fetched/decoded instruction
    input logic                     insn_valid_i,
    input logic [ImemAddrWidth-1:0] insn_addr_i,

    // Decoded instruction data, matching the "Decoding" section of the specification.
    input insn_dec_base_t insn_dec_base_i,
    input insn_dec_ctrl_t insn_dec_ctrl_i,

    // Base register file
    output logic [ 4:0] rf_base_wr_addr_o,
    output logic        rf_base_wr_en_o,
    output logic [31:0] rf_base_wr_data_o,

    output logic [ 4:0] rf_base_rd_addr_a_o,
    input  logic [31:0] rf_base_rd_data_a_i,

    output logic [ 4:0] rf_base_rd_addr_b_o,
    input  logic [31:0] rf_base_rd_data_b_i,

    // Execution units
    output alu_base_operation_t         alu_base_operation_o,
    output alu_base_comparison_t        alu_base_comparison_o,
    input  logic                 [31:0] alu_base_operation_result_i,
    input  logic                        alu_base_comparison_result_i
);


  logic running_q, running_d;

  assign done_o = insn_valid_i && insn_dec_ctrl_i.ecall_insn;

  always_comb begin
    running_d = running_q;
    insn_fetch_req_valid_o = 1'b0;
    insn_fetch_req_addr_o = start_addr_i;

    if (start_i) begin
      running_d = 1'b1;
      insn_fetch_req_addr_o = start_addr_i;
      insn_fetch_req_valid_o = 1'b01;
    end else if (running_q) begin
      insn_fetch_req_valid_o = 1'b1;
      insn_fetch_req_addr_o = insn_addr_i + 'd4;
    end

    if (done_o) begin
      running_d = 1'b0;
      insn_fetch_req_valid_o = 1'b0;
    end
    // TODO: Jumps/branches
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      running_q <= 1'b0;
    end else begin
      running_q <= running_d;
    end
  end

  assign rf_base_rd_addr_a_o = insn_dec_base_i.a;
  assign rf_base_rd_addr_b_o = insn_dec_base_i.b;

  // Base ALU Operand A MUX
  always_comb begin
    unique case (insn_dec_ctrl_i.op_a_sel)
      OpASelRegister: alu_base_operation_o.operand_a = rf_base_rd_data_a_i;
      default: alu_base_operation_o.operand_a = rf_base_rd_data_a_i;
    endcase
  end

  // Base ALU Operand B MUX
  always_comb begin
    unique case (insn_dec_ctrl_i.op_b_sel)
      OpBSelRegister: alu_base_operation_o.operand_b = rf_base_rd_data_b_i;
      OpBSelImmediate: alu_base_operation_o.operand_b = insn_dec_base_i.i;
      default: alu_base_operation_o.operand_b = rf_base_rd_data_b_i;
    endcase
  end

  assign alu_base_operation_o.op = insn_dec_ctrl_i.alu_op;

  assign alu_base_comparison_o.operand_a = rf_base_rd_data_a_i;
  assign alu_base_comparison_o.operand_b = rf_base_rd_data_b_i;
  // TODO: Choose comparison required for branch
  assign alu_base_comparison_o.op = ComparisonOpEq;

  // Register file write MUX
  // TODO: Switch between CSR/ALU/LSU writeback.
  assign rf_base_wr_en_o = insn_dec_ctrl_i.rf_we;
  assign rf_base_wr_addr_o = insn_dec_base_i.d;
  assign rf_base_wr_data_o = alu_base_operation_result_i;

endmodule
