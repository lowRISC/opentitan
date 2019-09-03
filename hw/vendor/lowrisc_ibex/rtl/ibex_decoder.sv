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
 */
module ibex_decoder #(
    parameter bit RV32E = 0,
    parameter bit RV32M = 1
) (
    // to/from controller
    output logic                 illegal_insn_o,        // illegal instr encountered
    output logic                 ebrk_insn_o,           // trap instr encountered
    output logic                 mret_insn_o,           // return from exception instr
                                                        // encountered
    output logic                 dret_insn_o,           // return from debug instr encountered
    output logic                 ecall_insn_o,          // syscall instr encountered
    output logic                 wfi_insn_o,            // wait for interrupt instr encountered
    output logic                 jump_set_o,            // jump taken set signal

    // from IF-ID pipeline register
    input  logic                 instr_new_i,           // instruction read is new
    input  logic [31:0]          instr_rdata_i,         // instruction read from memory/cache
    input  logic                 illegal_c_insn_i,      // compressed instruction decode failed

    // immediates
    output ibex_pkg::imm_a_sel_e imm_a_mux_sel_o,       // immediate selection for operand a
    output ibex_pkg::imm_b_sel_e imm_b_mux_sel_o,       // immediate selection for operand b
    output logic [31:0]          imm_i_type_o,
    output logic [31:0]          imm_s_type_o,
    output logic [31:0]          imm_b_type_o,
    output logic [31:0]          imm_u_type_o,
    output logic [31:0]          imm_j_type_o,
    output logic [31:0]          zimm_rs1_type_o,

    // register file
    output ibex_pkg::rf_wd_sel_e regfile_wdata_sel_o,   // RF write data selection
    output logic                 regfile_we_o,          // write enable for regfile
    output logic [4:0]           regfile_raddr_a_o,
    output logic [4:0]           regfile_raddr_b_o,
    output logic [4:0]           regfile_waddr_o,

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
    output ibex_pkg::md_op_e     multdiv_operator_o,
    output logic [1:0]           multdiv_signed_mode_o,

    // CSRs
    output logic                 csr_access_o,          // access to CSR
    output ibex_pkg::csr_op_e    csr_op_o,              // operation to perform on CSR
    output logic                 csr_pipe_flush_o,      // CSR-related pipeline flush

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
  logic        regfile_we;

  logic [31:0] instr;

  csr_op_e     csr_op;

  opcode_e     opcode;

  assign instr = instr_rdata_i;

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
  assign regfile_raddr_a_o = instr[`REG_S1]; // rs1
  assign regfile_raddr_b_o = instr[`REG_S2]; // rs2

  // destination register
  assign regfile_waddr_o   = instr[`REG_D]; // rd

  ////////////////////
  // Register check //
  ////////////////////
  if (RV32E) begin : gen_rv32e_reg_check_active
    assign illegal_reg_rv32e = ((regfile_raddr_a_o[4] & (alu_op_a_mux_sel_o == OP_A_REG_A)) |
                                (regfile_raddr_b_o[4] & (alu_op_b_mux_sel_o == OP_B_REG_B)) |
                                (regfile_waddr_o[4]   & regfile_we));
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

  /////////////////////////////////
  // CSR-related pipline flushes //
  /////////////////////////////////
  always_comb begin : csr_pipeline_flushes
    csr_pipe_flush_o = 1'b0;

    // A pipeline flush is needed to let the controller react after modifying certain CSRs:
    // - When enabling interrupts, pending IRQs become visible to the controller only during
    //   the next cycle. If during that cycle the core disables interrupts again, it does not
    //   see any pending IRQs and consequently does not start to handle interrupts.
    // - When modifying debug CSRs - TODO: Check if this is really needed
    if (csr_access_o == 1'b1 && (csr_op_o == CSR_OP_WRITE || csr_op_o == CSR_OP_SET)) begin
      if (csr_num_e'(instr[31:20]) == CSR_MSTATUS   ||
          csr_num_e'(instr[31:20]) == CSR_MIE) begin
        csr_pipe_flush_o = 1'b1;
      end
    end else if (csr_access_o == 1'b1 && csr_op_o != CSR_OP_READ) begin
      if (csr_num_e'(instr[31:20]) == CSR_DCSR      ||
          csr_num_e'(instr[31:20]) == CSR_DPC       ||
          csr_num_e'(instr[31:20]) == CSR_DSCRATCH0 ||
          csr_num_e'(instr[31:20]) == CSR_DSCRATCH1) begin
        csr_pipe_flush_o = 1'b1;
      end
    end
  end

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    jump_in_dec_o               = 1'b0;
    jump_set_o                  = 1'b0;
    branch_in_dec_o             = 1'b0;
    alu_operator_o              = ALU_SLTU;
    alu_op_a_mux_sel_o          = OP_A_IMM;
    alu_op_b_mux_sel_o          = OP_B_IMM;

    imm_a_mux_sel_o             = IMM_A_ZERO;
    imm_b_mux_sel_o             = IMM_B_I;

    mult_en_o                   = 1'b0;
    div_en_o                    = 1'b0;
    multdiv_operator_o          = MD_OP_MULL;
    multdiv_signed_mode_o       = 2'b00;

    regfile_wdata_sel_o         = RF_WD_EX;
    regfile_we                  = 1'b0;

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
        jump_in_dec_o         = 1'b1;
        if (instr_new_i) begin
          // Calculate jump target
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_J;
          alu_operator_o      = ALU_ADD;
          regfile_we          = 1'b0;
          jump_set_o          = 1'b1;
        end else begin
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
          regfile_we          = 1'b1;
        end
      end

      OPCODE_JALR: begin  // Jump and Link Register
        jump_in_dec_o         = 1'b1;
        if (instr_new_i) begin
          // Calculate jump target
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_I;
          alu_operator_o      = ALU_ADD;
          regfile_we          = 1'b0;
          jump_set_o          = 1'b1;
        end else begin
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
          regfile_we          = 1'b1;
        end
        if (instr[14:12] != 3'b0) begin
          illegal_insn = 1'b1;
        end
      end

      OPCODE_BRANCH: begin // Branch
        branch_in_dec_o       = 1'b1;
        // Check branch condition selection
        unique case (instr[14:12])
          3'b000:  alu_operator_o = ALU_EQ;
          3'b001:  alu_operator_o = ALU_NE;
          3'b100:  alu_operator_o = ALU_LT;
          3'b101:  alu_operator_o = ALU_GE;
          3'b110:  alu_operator_o = ALU_LTU;
          3'b111:  alu_operator_o = ALU_GEU;
          default: illegal_insn   = 1'b1;
        endcase
        if (instr_new_i) begin
          // Evaluate branch condition
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_REG_B;
        end else begin
          // Calculate jump target in EX
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_B;
          alu_operator_o      = ALU_ADD;
          regfile_we          = 1'b0;
        end
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;
        data_req_o         = 1'b1;
        data_we_o          = 1'b1;
        alu_operator_o     = ALU_ADD;

        if (!instr[14]) begin
          // offset from immediate
          imm_b_mux_sel_o     = IMM_B_S;
          alu_op_b_mux_sel_o  = OP_B_IMM;
        end else begin
          // Register offset is illegal since no register c available
          illegal_insn = 1'b1;
        end

        // store size
        unique case (instr[13:12])
          2'b00:   data_type_o  = 2'b10; // SB
          2'b01:   data_type_o  = 2'b01; // SH
          2'b10:   data_type_o  = 2'b00; // SW
          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_LOAD: begin
        alu_op_a_mux_sel_o  = OP_A_REG_A;
        data_req_o          = 1'b1;
        regfile_wdata_sel_o = RF_WD_LSU;
        regfile_we          = 1'b1;
        data_type_o         = 2'b00;

        // offset from immediate
        alu_operator_o      = ALU_ADD;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;

        // sign/zero extension
        data_sign_extension_o = ~instr[14];

        // load size
        unique case (instr[13:12])
          2'b00: data_type_o = 2'b10; // LB(U)
          2'b01: data_type_o = 2'b01; // LH(U)
          2'b10: begin
            data_type_o = 2'b00;      // LW
            if (instr[14]) begin
              illegal_insn = 1'b1;    // LWU does not exist
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
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMM_A_ZERO;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
        regfile_we          = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
        regfile_we          = 1'b1;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        alu_op_a_mux_sel_o  = OP_A_REG_A;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;
        regfile_we          = 1'b1;

        unique case (instr[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLT;  // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            alu_operator_o = ALU_SLL;  // Shift Left Logical by Immediate
            if (instr[31:25] != 7'b0) begin
              illegal_insn = 1'b1;
            end
          end

          3'b101: begin
            if (instr[31:25] == 7'b0) begin
              alu_operator_o = ALU_SRL;  // Shift Right Logical by Immediate
            end else if (instr[31:25] == 7'b010_0000) begin
              alu_operator_o = ALU_SRA;  // Shift Right Arithmetically by Immediate
            end else begin
              illegal_insn   = 1'b1;
            end
          end

          default: begin
            alu_operator_o = alu_op_e'({$bits(alu_op_e){1'bX}});
          end
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;
        regfile_we         = 1'b1;

        if (instr[31]) begin
          illegal_insn = 1'b1;
        end else begin
          unique case ({instr[30:25], instr[14:12]})
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

            // supported RV32M instructions
            {6'b00_0001, 3'b000}: begin // mul
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_MULL;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b001}: begin // mulh
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_MULH;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b010}: begin // mulhsu
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_MULH;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b01;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b011}: begin // mulhu
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_MULH;
              mult_en_o             = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b100}: begin // div
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_DIV;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b101}: begin // divu
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_DIV;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b110}: begin // rem
              alu_operator_o        = ALU_ADD;
              multdiv_operator_o    = MD_OP_REM;
              div_en_o              = RV32M ? 1'b1 : 1'b0;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = RV32M ? 1'b0 : 1'b1;
            end
            {6'b00_0001, 3'b111}: begin // remu
              alu_operator_o        = ALU_ADD;
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
        // For now, treat the fence (funct3 == 000) instruction as a nop.
        // This may not be correct in a system with caches and should be
        // revisited.
        // fence.i (funct3 == 001) was moved to a separate Zifencei extension
        // in the RISC-V ISA spec proposed for ratification, so we treat it as
        // an illegal instruction.
        if (instr[14:12] == 3'b000) begin
          alu_operator_o     = ALU_ADD; // nop
          alu_op_a_mux_sel_o = OP_A_REG_A;
          alu_op_b_mux_sel_o = OP_B_IMM;
          regfile_we         = 1'b0;
        end else begin
          illegal_insn       = 1'b1;
        end
      end

      OPCODE_SYSTEM: begin
        if (instr[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          alu_op_a_mux_sel_o = OP_A_REG_A;
          alu_op_b_mux_sel_o = OP_B_IMM;
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
          csr_access_o        = 1'b1;
          regfile_wdata_sel_o = RF_WD_CSR;
          regfile_we          = 1'b1;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_a_mux_sel_o     = IMM_A_Z;
          imm_b_mux_sel_o     = IMM_B_I;  // CSR address is encoded in I imm

          if (instr[14]) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            alu_op_a_mux_sel_o = OP_A_REG_A;
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
      regfile_we      = 1'b0;
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

  // make sure instructions accessing non-available registers in RV32E cause illegal
  // instruction exceptions
  assign illegal_insn_o = illegal_insn | illegal_reg_rv32e;

  // do not propgate regfile write enable if non-available registers are accessed in RV32E
  assign regfile_we_o = regfile_we & ~illegal_reg_rv32e;

endmodule // controller
