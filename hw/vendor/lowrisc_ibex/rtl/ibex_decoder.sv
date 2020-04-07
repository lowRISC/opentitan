// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_D  11:07

/**
 * Instruction decoder
 *
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

`include "prim_assert.sv"

module ibex_decoder #(
    parameter bit RV32E           = 0,
    parameter bit RV32M           = 1,
    parameter bit RV32B           = 0,
    parameter bit BranchTargetALU = 0
) (
    input  logic                 clk_i,
    input  logic                 rst_ni,

    // to/from controller
    output logic                 illegal_insn_o,        // illegal instr encountered
    output logic                 ebrk_insn_o,           // trap instr encountered
    output logic                 mret_insn_o,           // return from exception instr
                                                        // encountered
    output logic                 dret_insn_o,           // return from debug instr encountered
    output logic                 ecall_insn_o,          // syscall instr encountered
    output logic                 wfi_insn_o,            // wait for interrupt instr encountered
    output logic                 jump_set_o,            // jump taken set signal
    output logic                 icache_inval_o,

    // from IF-ID pipeline register
    input  logic                 instr_first_cycle_i,   // instruction read is in its first cycle
    input  logic [31:0]          instr_rdata_i,         // instruction read from memory/cache
    input  logic [31:0]          instr_rdata_alu_i,     // instruction read from memory/cache
                                                        // replicated to ease fan-out)

    input  logic                 illegal_c_insn_i,      // compressed instruction decode failed

    // immediates
    output ibex_pkg::imm_a_sel_e  imm_a_mux_sel_o,       // immediate selection for operand a
    output ibex_pkg::imm_b_sel_e  imm_b_mux_sel_o,       // immediate selection for operand b
    output ibex_pkg::op_a_sel_e   bt_a_mux_sel_o,        // branch target selection operand a
    output ibex_pkg::imm_b_sel_e  bt_b_mux_sel_o,        // branch target selection operand b
    output logic [31:0]           imm_i_type_o,
    output logic [31:0]           imm_s_type_o,
    output logic [31:0]           imm_b_type_o,
    output logic [31:0]           imm_u_type_o,
    output logic [31:0]           imm_j_type_o,
    output logic [31:0]           zimm_rs1_type_o,

    // register file
    output ibex_pkg::rf_wd_sel_e rf_wdata_sel_o,   // RF write data selection
    output logic                 rf_we_o,          // write enable for regfile
    output logic [4:0]           rf_raddr_a_o,
    output logic [4:0]           rf_raddr_b_o,
    output logic [4:0]           rf_waddr_o,
    output logic                 rf_ren_a_o,          // Instruction reads from RF addr A
    output logic                 rf_ren_b_o,          // Instruction reads from RF addr B

    // ALU
    output ibex_pkg::alu_op_e    alu_operator_o,        // ALU operation selection
    output ibex_pkg::op_a_sel_e  alu_op_a_mux_sel_o,    // operand a selection: reg value, PC,
                                                        // immediate or zero
    output ibex_pkg::op_b_sel_e  alu_op_b_mux_sel_o,    // operand b selection: reg value or
                                                        // immediate

    // MULT & DIV
    output logic                 mult_en_o,             // perform integer multiplication
    output logic                 div_en_o,              // perform integer division or
                                                        // remainder
    output logic                 multdiv_sel_o,

    output ibex_pkg::md_op_e     multdiv_operator_o,
    output logic [1:0]           multdiv_signed_mode_o,

    // CSRs
    output logic                 csr_access_o,          // access to CSR
    output ibex_pkg::csr_op_e    csr_op_o,              // operation to perform on CSR

    // LSU
    output logic                 data_req_o,            // start transaction to data memory
    output logic                 data_we_o,             // write enable
    output logic [1:0]           data_type_o,           // size of transaction: byte, half
                                                        // word or word
    output logic                 data_sign_extension_o, // sign extension for data read from
                                                        // memory

    // jump/branches
    output logic                 jump_in_dec_o,         // jump is being calculated in ALU
    output logic                 branch_in_dec_o
);

  import ibex_pkg::*;

  logic        illegal_insn;
  logic        illegal_reg_rv32e;
  logic        csr_illegal;
  logic        rf_we;

  logic [31:0] instr;
  logic [31:0] instr_alu;

  csr_op_e     csr_op;

  opcode_e     opcode;
  opcode_e     opcode_alu;

  // To help timing the flops containing the current instruction are replicated to reduce fan-out.
  // instr_alu is used to determine the ALU control logic and associated operand/imm select signals
  // as the ALU is often on the more critical timing paths. instr is used for everything else.
  assign instr     = instr_rdata_i;
  assign instr_alu = instr_rdata_alu_i;

  //////////////////////////////////////
  // Register and immediate selection //
  //////////////////////////////////////

  // immediate extraction and sign extension
  assign imm_i_type_o = { {20{instr[31]}}, instr[31:20] };
  assign imm_s_type_o = { {20{instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_b_type_o = { {19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type_o = { instr[31:12], 12'b0 };
  assign imm_j_type_o = { {12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulation (zero extended)
  assign zimm_rs1_type_o = { 27'b0, instr[`REG_S1] }; // rs1

  // source registers
  assign rf_raddr_a_o = instr[`REG_S1]; // rs1
  assign rf_raddr_b_o = instr[`REG_S2]; // rs2

  // destination register
  assign rf_waddr_o   = instr[`REG_D]; // rd

  ////////////////////
  // Register check //
  ////////////////////
  if (RV32E) begin : gen_rv32e_reg_check_active
    assign illegal_reg_rv32e = ((rf_raddr_a_o[4] & (alu_op_a_mux_sel_o == OP_A_REG_A)) |
                                (rf_raddr_b_o[4] & (alu_op_b_mux_sel_o == OP_B_REG_B)) |
                                (rf_waddr_o[4]   & rf_we));
  end else begin : gen_rv32e_reg_check_inactive
    assign illegal_reg_rv32e = 1'b0;
  end

  ///////////////////////
  // CSR operand check //
  ///////////////////////
  always_comb begin : csr_operand_check
    csr_op_o = csr_op;

    // CSRRSI/CSRRCI must not write 0 to CSRs (uimm[4:0]=='0)
    // CSRRS/CSRRC must not write from x0 to CSRs (rs1=='0)
    if ((csr_op == CSR_OP_SET || csr_op == CSR_OP_CLEAR) &&
        instr[`REG_S1] == '0) begin
      csr_op_o = CSR_OP_READ;
    end
  end

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    jump_in_dec_o               = 1'b0;
    jump_set_o                  = 1'b0;
    branch_in_dec_o             = 1'b0;
    icache_inval_o              = 1'b0;

    mult_en_o                   = 1'b0;
    div_en_o                    = 1'b0;
    multdiv_operator_o          = MD_OP_MULL;
    multdiv_signed_mode_o       = 2'b00;

    rf_wdata_sel_o              = RF_WD_EX;
    rf_we                       = 1'b0;
    rf_ren_a_o                  = 1'b0;
    rf_ren_b_o                  = 1'b0;

    csr_access_o                = 1'b0;
    csr_illegal                 = 1'b0;
    csr_op                      = CSR_OP_READ;

    data_we_o                   = 1'b0;
    data_type_o                 = 2'b00;
    data_sign_extension_o       = 1'b0;
    data_req_o                  = 1'b0;

    illegal_insn                = 1'b0;
    ebrk_insn_o                 = 1'b0;
    mret_insn_o                 = 1'b0;
    dret_insn_o                 = 1'b0;
    ecall_insn_o                = 1'b0;
    wfi_insn_o                  = 1'b0;

    opcode                      = opcode_e'(instr[6:0]);

    unique case (opcode)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin   // Jump and Link
        jump_in_dec_o      = 1'b1;

        if (instr_first_cycle_i) begin
          // Calculate jump target (and store PC + 4 if BranchTargetALU is configured)
          rf_we            = BranchTargetALU;
          jump_set_o       = 1'b1;
        end else begin
          // Calculate and store PC+4
          rf_we            = 1'b1;
        end
      end

      OPCODE_JALR: begin  // Jump and Link Register
        jump_in_dec_o      = 1'b1;

        if (instr_first_cycle_i) begin
          // Calculate jump target (and store PC + 4 if BranchTargetALU is configured)
          rf_we            = BranchTargetALU;
          jump_set_o       = 1'b1;
        end else begin
          // Calculate and store PC+4
          rf_we            = 1'b1;
        end
        if (instr[14:12] != 3'b0) begin
          illegal_insn = 1'b1;
        end

        rf_ren_a_o = 1'b1;
      end

      OPCODE_BRANCH: begin // Branch
        branch_in_dec_o       = 1'b1;
        // Check branch condition selection
        unique case (instr[14:12])
          3'b000,
          3'b001,
          3'b100,
          3'b101,
          3'b110,
          3'b111:  illegal_insn = 1'b0;
          default: illegal_insn = 1'b1;
        endcase

        rf_ren_a_o = 1'b1;
        rf_ren_b_o = 1'b1;
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        rf_ren_a_o         = 1'b1;
        rf_ren_b_o         = 1'b1;
        data_req_o         = 1'b1;
        data_we_o          = 1'b1;

        if (instr[14]) begin
          illegal_insn = 1'b1;
        end

        // store size
        unique case (instr[13:12])
          2'b00:   data_type_o  = 2'b10; // sb
          2'b01:   data_type_o  = 2'b01; // sh
          2'b10:   data_type_o  = 2'b00; // sw
          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_LOAD: begin
        rf_ren_a_o          = 1'b1;
        data_req_o          = 1'b1;
        data_type_o         = 2'b00;

        // sign/zero extension
        data_sign_extension_o = ~instr[14];

        // load size
        unique case (instr[13:12])
          2'b00: data_type_o = 2'b10; // lb(u)
          2'b01: data_type_o = 2'b01; // lh(u)
          2'b10: begin
            data_type_o = 2'b00;      // lw
            if (instr[14]) begin
              illegal_insn = 1'b1;    // lwu does not exist
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        rf_we            = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        rf_we            = 1'b1;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        rf_ren_a_o       = 1'b1;
        rf_we            = 1'b1;

        unique case (instr[14:12])
          3'b000,
          3'b010,
          3'b011,
          3'b100,
          3'b110,
          3'b111: illegal_insn = 1'b0;

          3'b001: begin
            unique case (instr[31:25])
              7'b000_0000: illegal_insn = 1'b0;                 // slli
              7'b001_0000: illegal_insn = RV32B ? 1'b0 : 1'b1;  // sloi
              7'b011_0000: begin
                unique case(instr[24:20])
                  5'b00000,                                     // clz
                  5'b00001,                                     // ctz
                  5'b00010: illegal_insn = RV32B ? 1'b0 : 1'b1; // pcnt
                  default: illegal_insn = 1'b1;
                endcase
              end
              default : illegal_insn = 1'b1;
            endcase
          end

          3'b101: begin
            unique case (instr[31:25])
              7'b000_0000,                                      // srli
              7'b010_0000: illegal_insn = 1'b0;                 // srai

              7'b001_0000,                                      // sroi
              7'b011_0000: illegal_insn = RV32B ? 1'b0 : 1'b1;  // rori

              7'b011_0100: begin
                unique case(instr[24:20])
                  5'b11111,                                     // rev
                  5'b11000,                                     // rev8
                  5'b00111: illegal_insn = RV32B ? 1'b0 : 1'b1; // orc.b

                  default: illegal_insn = 1'b1;
                endcase
              end
              default: illegal_insn = 1'b1;
            endcase
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        rf_ren_a_o      = 1'b1;
        rf_ren_b_o      = 1'b1;
        rf_we           = 1'b1;

        if (instr[31]) begin
          illegal_insn = 1'b1;
        end else begin
          unique case ({instr[30:25], instr[14:12]})
            // RV32I ALU operations
            {6'b00_0000, 3'b000},
            {6'b10_0000, 3'b000},
            {6'b00_0000, 3'b010},
            {6'b00_0000, 3'b011},
            {6'b00_0000, 3'b100},
            {6'b00_0000, 3'b110},
            {6'b00_0000, 3'b111},
            {6'b00_0000, 3'b001},
            {6'b00_0000, 3'b101},
            {6'b10_0000, 3'b101}: illegal_insn = 1'b0;

            // supported RV32B instructions (zbb)
            {6'b10_0000, 3'b111}, // andn
            {6'b10_0000, 3'b110}, // orn
            {6'b10_0000, 3'b100}, // xnor
            {6'b01_0000, 3'b001}, // slo
            {6'b01_0000, 3'b101}, // sro
            {6'b11_0000, 3'b001}, // rol
            {6'b11_0000, 3'b101}, // ror
            {6'b00_0101, 3'b100}, // min
            {6'b00_0101, 3'b101}, // max
            {6'b00_0101, 3'b110}, // minu
            {6'b00_0101, 3'b111}, // maxu
            {6'b00_0100, 3'b100}, // pack
            {6'b10_0100, 3'b100}, // packu
            {6'b00_0100, 3'b111}: illegal_insn = RV32B ? 1'b0 : 1'b1; // packh

            // supported RV32M instructions
            {6'b00_0001, 3'b000}: begin // mul
              multdiv_operator_o    = MD_OP_MULL;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b001}: begin // mulh
              multdiv_operator_o    = MD_OP_MULH;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b010}: begin // mulhsu
              multdiv_operator_o    = MD_OP_MULH;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b01;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b011}: begin // mulhu
              multdiv_operator_o    = MD_OP_MULH;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b100}: begin // div
              multdiv_operator_o    = MD_OP_DIV;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b101}: begin // divu
              multdiv_operator_o    = MD_OP_DIV;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b110}: begin // rem
              multdiv_operator_o    = MD_OP_REM;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b111}: begin // remu
              multdiv_operator_o    = MD_OP_REM;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        // For now, treat the FENCE (funct3 == 000) instruction as a NOP.  This may not be correct
        // in a system with caches and should be revisited.
        // FENCE.I will flush the IF stage and prefetch buffer (or ICache) but nothing else.
        unique case (instr[14:12])
          3'b000: begin
            rf_we           = 1'b0;
          end
          3'b001: begin
            // FENCE.I is implemented as a jump to the next PC, this gives the required flushing
            // behaviour (iside prefetch buffer flushed and response to any outstanding iside
            // requests will be ignored).
            // If present, the ICache will also be flushed.
            jump_in_dec_o   = 1'b1;

            rf_we           = 1'b0;

            if (instr_first_cycle_i) begin
              jump_set_o       = 1'b1;
              icache_inval_o   = 1'b1;
            end
          end
          default: begin
            illegal_insn       = 1'b1;
          end
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          unique case (instr[31:20])
            12'h000:  // ECALL
              // environment (system) call
              ecall_insn_o = 1'b1;

            12'h001:  // ebreak
              // debugger trap
              ebrk_insn_o = 1'b1;

            12'h302:  // mret
              mret_insn_o = 1'b1;

            12'h7b2:  // dret
              dret_insn_o = 1'b1;

            12'h105:  // wfi
              wfi_insn_o = 1'b1;

            default:
              illegal_insn = 1'b1;
          endcase

          // rs1 and rd must be 0
          if (instr[`REG_S1] != 5'b0 || instr[`REG_D] != 5'b0) begin
            illegal_insn = 1'b1;
          end
        end else begin
          // instruction to read/modify CSR
          csr_access_o     = 1'b1;
          rf_wdata_sel_o   = RF_WD_CSR;
          rf_we            = 1'b1;

          if (~instr[14]) begin
            rf_ren_a_o         = 1'b1;
          end

          unique case (instr[13:12])
            2'b01:   csr_op = CSR_OP_WRITE;
            2'b10:   csr_op = CSR_OP_SET;
            2'b11:   csr_op = CSR_OP_CLEAR;
            default: csr_illegal = 1'b1;
          endcase

          illegal_insn = csr_illegal;
        end

      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase

    // make sure illegal compressed instructions cause illegal instruction exceptions
    if (illegal_c_insn_i) begin
      illegal_insn = 1'b1;
    end

    // make sure illegal instructions detected in the decoder do not propagate from decoder
    // into register file, LSU, EX, WB, CSRs, PC
    // NOTE: instructions can also be detected to be illegal inside the CSRs (upon accesses with
    // insufficient privileges), or when accessing non-available registers in RV32E,
    // these cases are not handled here
    if (illegal_insn) begin
      rf_we           = 1'b0;
      data_req_o      = 1'b0;
      data_we_o       = 1'b0;
      mult_en_o       = 1'b0;
      div_en_o        = 1'b0;
      jump_in_dec_o   = 1'b0;
      jump_set_o      = 1'b0;
      branch_in_dec_o = 1'b0;
      csr_access_o    = 1'b0;
    end
  end

  /////////////////////////////
  // Decoder for ALU control //
  /////////////////////////////

  always_comb begin
    alu_operator_o     = ALU_SLTU;
    alu_op_a_mux_sel_o = OP_A_IMM;
    alu_op_b_mux_sel_o = OP_B_IMM;

    imm_a_mux_sel_o    = IMM_A_ZERO;
    imm_b_mux_sel_o    = IMM_B_I;

    bt_a_mux_sel_o     = OP_A_CURRPC;
    bt_b_mux_sel_o     = IMM_B_I;

    multdiv_sel_o      = 1'b0;

    opcode_alu         = opcode_e'(instr_alu[6:0]);

    unique case (opcode_alu)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin // Jump and Link
        if (BranchTargetALU) begin
          bt_a_mux_sel_o = OP_A_CURRPC;
          bt_b_mux_sel_o = IMM_B_J;
        end

        // Jumps take two cycles without the BTALU
        if (instr_first_cycle_i && !BranchTargetALU) begin
          // Calculate jump target
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_J;
          alu_operator_o      = ALU_ADD;
        end else begin
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        end
      end

      OPCODE_JALR: begin // Jump and Link Register
        if (BranchTargetALU) begin
          bt_a_mux_sel_o = OP_A_REG_A;
          bt_b_mux_sel_o = IMM_B_I;
        end

        // Jumps take two cycles without the BTALU
        if (instr_first_cycle_i && !BranchTargetALU) begin
          // Calculate jump target
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_I;
          alu_operator_o      = ALU_ADD;
        end else begin
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        end
      end

      OPCODE_BRANCH: begin // Branch
        // Check branch condition selection
        unique case (instr_alu[14:12])
          3'b000:  alu_operator_o = ALU_EQ;
          3'b001:  alu_operator_o = ALU_NE;
          3'b100:  alu_operator_o = ALU_LT;
          3'b101:  alu_operator_o = ALU_GE;
          3'b110:  alu_operator_o = ALU_LTU;
          3'b111:  alu_operator_o = ALU_GEU;
          default: ;
        endcase

        if (BranchTargetALU) begin
          // With branch target ALU the main ALU evaluates the branch condition and the branch
          // target ALU calculates the target (which is controlled in a seperate block below)
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_REG_B;
          bt_a_mux_sel_o      = OP_A_CURRPC;
          bt_b_mux_sel_o      = IMM_B_B;
        end else begin
          // Without branch target ALU, a branch is a two-stage operation using the Main ALU in both
          // stages
          if (instr_first_cycle_i) begin
            // First evaluate the branch condition
            alu_op_a_mux_sel_o  = OP_A_REG_A;
            alu_op_b_mux_sel_o  = OP_B_REG_B;
          end else begin
            // Then calculate jump target
            alu_op_a_mux_sel_o  = OP_A_CURRPC;
            alu_op_b_mux_sel_o  = OP_B_IMM;
            imm_b_mux_sel_o     = IMM_B_B;
            alu_operator_o      = ALU_ADD;
          end
        end
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;
        alu_operator_o     = ALU_ADD;

        if (!instr_alu[14]) begin
          // offset from immediate
          imm_b_mux_sel_o     = IMM_B_S;
          alu_op_b_mux_sel_o  = OP_B_IMM;
        end
      end

      OPCODE_LOAD: begin
        alu_op_a_mux_sel_o  = OP_A_REG_A;

        // offset from immediate
        alu_operator_o      = ALU_ADD;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMM_A_ZERO;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        alu_op_a_mux_sel_o  = OP_A_REG_A;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;

        unique case (instr_alu[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLT;  // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            if (RV32B) begin
              // We don't factor in instr[31] here to make the ALU decoder more symmetric for
              // Reg-Reg and Reg-Imm ALU operations. Instr[31] is only needed to detect illegal
              // encodings for Reg-Reg ALU operations (see non-ALU decoder).
              unique case (instr[30:25])
                6'b00_0000: alu_operator_o = ALU_SLL;    // Shift Left Logical by Immediate
                6'b01_0000: alu_operator_o = ALU_SLO;    // Shift Left Ones by Immediate
                6'b11_0000: begin
                  unique case (instr[24:20])
                    5'b00000: alu_operator_o = ALU_CLZ;  // Count Leading Zeros
                    5'b00001: alu_operator_o = ALU_CTZ;  // Count Trailing Zeros
                    5'b00010: alu_operator_o = ALU_PCNT; // Count Set Bits
                    default: ;
                  endcase
                end

                default: ;
              endcase
            end else begin
              alu_operator_o = ALU_SLL;                  // Shift Left Logical by Immediate
            end
          end

          3'b101: begin
            if (RV32B) begin
              // We don't factor in instr[31] here to make the ALU decoder more symmetric for
              // Reg-Reg and Reg-Imm ALU operations. Instr[31] is only needed to detect illegal
              // encodings for Reg-Reg ALU operations (see non-ALU decoder).
              unique case (instr_alu[30:25])
                6'b00_0000: alu_operator_o = ALU_SRL; // Shift Right Logical by Immediate
                6'b10_0000: alu_operator_o = ALU_SRA; // Shift Right Arithmetically by Immediate
                6'b01_0000: alu_operator_o = ALU_SRO; // Shift Right Ones by Immediate
                6'b11_0000: alu_operator_o = ALU_ROR; // Rotate Right by Immediate
                6'b11_0100: begin
                  if (instr_alu[24:20] == 5'b11111) begin
                    alu_operator_o = ALU_REV;         // Reverse
                  end else if (instr_alu[24:20] == 5'b11000) begin
                    alu_operator_o = ALU_REV8;        // Byte-swap
                  end
                end
                6'b01_0100: begin
                  if (instr_alu[24:20] == 5'b00111) begin
                    alu_operator_o = ALU_ORCB;        // Byte-wise Reverse and Or-Combine
                  end
                end
                default: ;
              endcase

            end else begin
              if (instr_alu[31:25] == 7'b0) begin
                alu_operator_o = ALU_SRL;            // Shift Right Logical by Immediate
              end else if (instr_alu[31:25] == 7'b010_0000) begin
                alu_operator_o = ALU_SRA;            // Shift Right Arithmetically by Immediate
              end
            end
          end

          default: ;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;

        unique case ({instr_alu[30:25], instr_alu[14:12]})
          // RV32I ALU operations
          {6'b00_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
          {6'b10_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
          {6'b00_0000, 3'b010}: alu_operator_o = ALU_SLT;   // Set Lower Than
          {6'b00_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
          {6'b00_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
          {6'b00_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
          {6'b00_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
          {6'b00_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
          {6'b00_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
          {6'b10_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

          // RV32B ALU Operations
          {6'b01_0000, 3'b001}: if (RV32B) alu_operator_o = ALU_SLO;   // Shift Left Ones
          {6'b01_0000, 3'b101}: if (RV32B) alu_operator_o = ALU_SRO;   // Shift Right Ones
          {6'b11_0000, 3'b001}: if (RV32B) alu_operator_o = ALU_ROL;   // Rotate Left
          {6'b11_0000, 3'b101}: if (RV32B) alu_operator_o = ALU_ROR;   // Rotate Right

          {6'b00_0101, 3'b100}: if (RV32B) alu_operator_o = ALU_MIN;   // Minimum
          {6'b00_0101, 3'b101}: if (RV32B) alu_operator_o = ALU_MAX;   // Maximum
          {6'b00_0101, 3'b110}: if (RV32B) alu_operator_o = ALU_MINU;  // Minimum Unsigned
          {6'b00_0101, 3'b111}: if (RV32B) alu_operator_o = ALU_MAXU;  // Maximum Unsigned

          {6'b00_0100, 3'b100}: if (RV32B) alu_operator_o = ALU_PACK;  // Pack Lower Halves
          {6'b10_0100, 3'b100}: if (RV32B) alu_operator_o = ALU_PACKU; // Pack Upper Halves
          {6'b00_0100, 3'b111}: if (RV32B) alu_operator_o = ALU_PACKH; // Pack LSB Bytes

          {6'b10_0000, 3'b100}: if (RV32B) alu_operator_o = ALU_XNOR;  // Xnor
          {6'b10_0000, 3'b110}: if (RV32B) alu_operator_o = ALU_ORN;   // Orn
          {6'b10_0000, 3'b111}: if (RV32B) alu_operator_o = ALU_ANDN;  // Andn

          // supported RV32M instructions, all use the same ALU operation
          {6'b00_0001, 3'b000}, // mul
          {6'b00_0001, 3'b001}, // mulh
          {6'b00_0001, 3'b010}, // mulhsu
          {6'b00_0001, 3'b011}, // mulhu
          {6'b00_0001, 3'b100}, // div
          {6'b00_0001, 3'b101}, // divu
          {6'b00_0001, 3'b110}, // rem
          {6'b00_0001, 3'b111}: begin // remu
            multdiv_sel_o         = 1'b1;
            alu_operator_o        = ALU_ADD;
          end

          default: ;
        endcase
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        // For now, treat the FENCE (funct3 == 000) instruction as a NOP.  This may not be correct
        // in a system with caches and should be revisited.
        // FENCE.I will flush the IF stage and prefetch buffer but nothing else.
        unique case (instr_alu[14:12])
          3'b000: begin
            alu_operator_o     = ALU_ADD; // nop
            alu_op_a_mux_sel_o = OP_A_REG_A;
            alu_op_b_mux_sel_o = OP_B_IMM;
          end
          3'b001: begin
            if (BranchTargetALU) begin
              bt_a_mux_sel_o     = OP_A_CURRPC;
              bt_b_mux_sel_o     = IMM_B_INCR_PC;
            end else begin
              alu_op_a_mux_sel_o = OP_A_CURRPC;
              alu_op_b_mux_sel_o = OP_B_IMM;
              imm_b_mux_sel_o    = IMM_B_INCR_PC;
              alu_operator_o     = ALU_ADD;
            end
          end
          default: ;
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr_alu[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          alu_op_a_mux_sel_o = OP_A_REG_A;
          alu_op_b_mux_sel_o = OP_B_IMM;
        end else begin
          // instruction to read/modify CSR
          alu_op_b_mux_sel_o = OP_B_IMM;
          imm_a_mux_sel_o    = IMM_A_Z;
          imm_b_mux_sel_o    = IMM_B_I;  // CSR address is encoded in I imm

          if (instr_alu[14]) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            alu_op_a_mux_sel_o = OP_A_REG_A;
          end
        end

      end
      default: ;
    endcase
  end

  // make sure instructions accessing non-available registers in RV32E cause illegal
  // instruction exceptions
  assign illegal_insn_o = illegal_insn | illegal_reg_rv32e;

  // do not propgate regfile write enable if non-available registers are accessed in RV32E
  assign rf_we_o = rf_we & ~illegal_reg_rv32e;

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexRegImmAluOpKnown, (opcode == OPCODE_OP_IMM) |->
      !$isunknown(instr[14:12]))
endmodule // controller
