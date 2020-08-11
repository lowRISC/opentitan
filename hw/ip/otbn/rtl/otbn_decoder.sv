// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN instruction Decoder
 */
module otbn_decoder
import otbn_pkg::*;
(
    // For assertions only.
    input logic clk_i,
    input logic rst_ni,

    // instruction data to be decoded
    input logic [31:0] insn_fetch_resp_data_i,
    input logic        insn_fetch_resp_valid_i,

    // Decoded instruction
    output logic insn_valid_o,
    output logic insn_illegal_o,

    // Decoded instruction data, matching the "Decoding" section of the specification.
    output insn_dec_base_t insn_dec_base_o,

    // Additional control signals
    output insn_dec_ctrl_t insn_dec_ctrl_o
);

  logic illegal_insn;
  logic rf_we;

  logic [31:0] insn;
  logic [31:0] insn_alu;

  // Source/Destination register instruction index
  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rd;

  insn_opcode_e opcode;
  insn_opcode_e opcode_alu;

  // To help timing the flops containing the current instruction are replicated to reduce fan-out.
  // insn_alu is used to determine the ALU control logic and associated operand/imm select signals
  // as the ALU is often on the more critical timing paths. insn is used for everything else.
  // TODO: Actually replicate flops, if needed.
  assign insn = insn_fetch_resp_data_i;
  assign insn_alu = insn_fetch_resp_data_i;

  //////////////////////////////////////
  // Register and immediate selection //
  //////////////////////////////////////
  imm_a_sel_e imm_a_mux_sel;  // immediate selection for operand a
  imm_b_sel_e imm_b_mux_sel;  // immediate selection for operand b

  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;

  alu_op_e alu_operator;  // ALU operation selection
  op_a_sel_e alu_op_a_mux_sel;  // operand a selection: reg value, PC, immediate or zero
  op_b_sel_e alu_op_b_mux_sel;  // operand b selection: reg value or immediate

  logic rf_ren_a;
  logic rf_ren_b;

  // immediate extraction and sign extension
  assign imm_i_type = {{20{insn[31]}}, insn[31:20]};
  assign imm_s_type = {{20{insn[31]}}, insn[31:25], insn[11:7]};
  assign imm_b_type = {{19{insn[31]}}, insn[31], insn[7], insn[30:25], insn[11:8], 1'b0};
  assign imm_u_type = {insn[31:12], 12'b0};
  assign imm_j_type = {{12{insn[31]}}, insn[19:12], insn[20], insn[30:21], 1'b0};

  // source registers
  assign insn_rs1 = insn[19:15];
  assign insn_rs2 = insn[24:20];

  // destination register
  assign insn_rd = insn[11:7];

  insn_subset_e insn_subset;
  rf_wd_sel_e rf_wdata_sel;

  logic ecall_insn;

  // Reduced main ALU immediate MUX for Operand B
  logic [31:0] imm_b;
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel)
      ImmBI: imm_b = imm_i_type;
      ImmBS: imm_b = imm_s_type;
      ImmBU: imm_b = imm_u_type;
      default: imm_b = 32'h4;
    endcase
  end

  assign insn_valid_o = insn_fetch_resp_valid_i & ~illegal_insn;
  assign insn_illegal_o = insn_fetch_resp_valid_i & illegal_insn;

  assign insn_dec_base_o = '{a: insn_rs1, b: insn_rs2, d: insn_rd, i: imm_b};

  assign insn_dec_ctrl_o = '{subset: insn_subset, op_a_sel: alu_op_a_mux_sel,
                             op_b_sel: alu_op_b_mux_sel, alu_op: alu_operator, rf_we: rf_we,
                             rf_wdata_sel: rf_wdata_sel, ecall_insn: ecall_insn};

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    rf_wdata_sel = RfWdSelEx;
    rf_we = 1'b0;
    rf_ren_a = 1'b0;
    rf_ren_b = 1'b0;

    illegal_insn = 1'b0;
    ecall_insn = 1'b0;

    opcode = insn_opcode_e'(insn[6:0]);

    unique case (opcode)
      /////////
      // ALU //
      /////////

      InsnOpcodeBaseLui: begin  // Load Upper Immediate
        insn_subset = InsnSubsetBase;
        rf_we = 1'b1;
      end

      InsnOpcodeBaseOpImm: begin  // Register-Immediate ALU Operations
        insn_subset = InsnSubsetBase;
        rf_ren_a = 1'b1;
        rf_we = 1'b1;

        unique case (insn[14:12])
          3'b000, 3'b010, 3'b011, 3'b100, 3'b110, 3'b111: illegal_insn = 1'b0;

          3'b001: begin
            unique case (insn[31:27])
              5'b0_0000: illegal_insn = 1'b0;  // slli
              default: illegal_insn = 1'b1;
            endcase
          end

          3'b101: begin
            if (!insn[26]) begin
              unique case (insn[31:27])
                5'b0_0000,  // srli
                5'b0_1000:
                illegal_insn = 1'b0;  // srai

                default: illegal_insn = 1'b1;
              endcase
            end
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      InsnOpcodeBaseOp: begin  // Register-Register ALU operation
        insn_subset = InsnSubsetBase;
        rf_ren_a = 1'b1;
        rf_ren_b = 1'b1;
        rf_we = 1'b1;
        if ({
          insn[26], insn[13:12]
        } != {
          1'b1, 2'b01
        }) begin
          unique case ({
            insn[31:25], insn[14:12]
          })
            // RV32I ALU operations
            {
              7'b000_0000, 3'b000
            }, {
              7'b010_0000, 3'b000
            }, {
              7'b000_0000, 3'b010
            }, {
              7'b000_0000, 3'b011
            }, {
              7'b000_0000, 3'b100
            }, {
              7'b000_0000, 3'b110
            }, {
              7'b000_0000, 3'b111
            }, {
              7'b000_0000, 3'b001
            }, {
              7'b000_0000, 3'b101
            }, {
              7'b010_0000, 3'b101
            } :
            illegal_insn = 1'b0;
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
      end


      InsnOpcodeBaseSystem: begin
        insn_subset = InsnSubsetBase;
        if (insn[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          unique case (insn[31:20])
            12'h000:  // ECALL
            ecall_insn = 1'b1;

            default: illegal_insn = 1'b1;
          endcase

          // rs1 and rd must be 0
          if (insn_rs1 != 5'b0 || insn_rd != 5'b0) begin
            illegal_insn = 1'b1;
          end
        end else begin
          illegal_insn = 1'b1;
        end
      end

      default: illegal_insn = 1'b1;
    endcase


    // make sure illegal instructions detected in the decoder do not propagate from decoder
    // NOTE: instructions can also be detected to be illegal inside the CSRs (upon accesses with
    // insufficient privileges). These cases are not handled here.
    if (illegal_insn) begin
      rf_we = 1'b0;
    end
  end

  /////////////////////////////
  // Decoder for ALU control //
  /////////////////////////////

  always_comb begin
    alu_operator = AluOpAdd;
    alu_op_a_mux_sel = OpASelImmediate;
    alu_op_b_mux_sel = OpBSelImmediate;

    imm_a_mux_sel = ImmAZero;
    imm_b_mux_sel = ImmBI;

    opcode_alu = insn_opcode_e'(insn_alu[6:0]);

    unique case (opcode_alu)
      /////////
      // ALU //
      /////////

      InsnOpcodeBaseLui: begin  // Load Upper Immediate
        alu_op_a_mux_sel = OpASelImmediate;
        alu_op_b_mux_sel = OpBSelImmediate;
        imm_a_mux_sel = ImmAZero;
        imm_b_mux_sel = ImmBU;
        alu_operator = AluOpAdd;
      end

      InsnOpcodeBaseAuipc: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel = OpASelCurrPc;
        alu_op_b_mux_sel = OpBSelImmediate;
        imm_b_mux_sel = ImmBU;
        alu_operator = AluOpAdd;
      end

      InsnOpcodeBaseOpImm: begin  // Register-Immediate ALU Operations
        alu_op_a_mux_sel = OpASelRegister;
        alu_op_b_mux_sel = OpBSelImmediate;
        imm_b_mux_sel = ImmBI;

        unique case (insn_alu[14:12])
          3'b000: alu_operator = AluOpAdd;  // Add Immediate
          3'b100: alu_operator = AluOpXor;  // Exclusive Or with Immediate
          3'b110: alu_operator = AluOpOr;  // Or with Immediate
          3'b111: alu_operator = AluOpAnd;  // And with Immediate

          3'b001: begin
            alu_operator = AluOpSll;  // Shift Left Logical by Immediate
          end

          3'b101: begin
            if (insn_alu[31:27] == 5'b0_0000) begin
              alu_operator = AluOpSrl;  // Shift Right Logical by Immediate
            end else if (insn_alu[31:27] == 5'b0_1000) begin
              alu_operator = AluOpSra;  // Shift Right Arithmetically by Immediate
            end
          end

          default: ;
        endcase
      end

      InsnOpcodeBaseOp: begin  // Register-Register ALU operation
        alu_op_a_mux_sel = OpASelRegister;
        alu_op_b_mux_sel = OpBSelRegister;

        if (!insn_alu[26]) begin
          unique case ({
            insn_alu[31:25], insn_alu[14:12]
          })
            // RV32I ALU operations
            {
              7'b000_0000, 3'b000
            } :
            alu_operator = AluOpAdd;  // Add
            {7'b010_0000, 3'b000} : alu_operator = AluOpSub;  // Sub
            {7'b000_0000, 3'b100} : alu_operator = AluOpXor;  // Xor
            {7'b000_0000, 3'b110} : alu_operator = AluOpOr;  // Or
            {7'b000_0000, 3'b111} : alu_operator = AluOpAnd;  // And
            {7'b000_0000, 3'b001} : alu_operator = AluOpSll;  // Shift Left Logical
            {7'b000_0000, 3'b101} : alu_operator = AluOpSrl;  // Shift Right Logical
            {7'b010_0000, 3'b101} : alu_operator = AluOpSra;  // Shift Right Arithmetic
            default: ;
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      InsnOpcodeBaseSystem: begin
        if (insn_alu[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          alu_op_a_mux_sel = OpASelRegister;
          alu_op_b_mux_sel = OpBSelImmediate;
        end

      end
      default: ;
    endcase
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexRegImmAluOpKnown, (opcode == InsnOpcodeBaseOpImm) |-> !$isunknown(insn[14:12]))
endmodule
