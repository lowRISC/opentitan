// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Instruction decoder
 *
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

`include "prim_assert.sv"

module ibex_decoder #(
  parameter bit RV32E               = 0,
  parameter ibex_pkg::rv32m_e RV32M = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B = ibex_pkg::RV32BNone,
  parameter bit BranchTargetALU     = 0
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
  input  logic                 branch_taken_i,        // registered branch decision
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
  output logic                 alu_multicycle_o,      // ternary bitmanip instruction

  // MULT & DIV
  output logic                 mult_en_o,             // perform integer multiplication
  output logic                 div_en_o,              // perform integer division or remainder
  output logic                 mult_sel_o,            // as above but static, for data muxes
  output logic                 div_sel_o,             // as above but static, for data muxes

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
  logic [9:0]  unused_instr_alu;
  // Source/Destination register instruction index
  logic [4:0] instr_rs1;
  logic [4:0] instr_rs2;
  logic [4:0] instr_rs3;
  logic [4:0] instr_rd;

  logic        use_rs3_d;
  logic        use_rs3_q;

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
  assign zimm_rs1_type_o = { 27'b0, instr_rs1 }; // rs1

  if (RV32B != RV32BNone) begin : gen_rs3_flop
    // the use of rs3 is known one cycle ahead.
    always_ff  @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        use_rs3_q <= 1'b0;
      end else begin
        use_rs3_q <= use_rs3_d;
      end
    end
  end else begin : gen_no_rs3_flop
    logic unused_clk;
    logic unused_rst_n;

    // Clock and reset unused when there's no rs3 flop
    assign unused_clk = clk_i;
    assign unused_rst_n = rst_ni;

    // always zero
    assign use_rs3_q = use_rs3_d;
  end

  // source registers
  assign instr_rs1 = instr[19:15];
  assign instr_rs2 = instr[24:20];
  assign instr_rs3 = instr[31:27];
  assign rf_raddr_a_o = (use_rs3_q & ~instr_first_cycle_i) ? instr_rs3 : instr_rs1; // rs3 / rs1
  assign rf_raddr_b_o = instr_rs2; // rs2

  // destination register
  assign instr_rd = instr[11:7];
  assign rf_waddr_o   = instr_rd; // rd

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
        instr_rs1 == '0) begin
      csr_op_o = CSR_OP_READ;
    end
  end

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    jump_in_dec_o         = 1'b0;
    jump_set_o            = 1'b0;
    branch_in_dec_o       = 1'b0;
    icache_inval_o        = 1'b0;

    multdiv_operator_o    = MD_OP_MULL;
    multdiv_signed_mode_o = 2'b00;

    rf_wdata_sel_o        = RF_WD_EX;
    rf_we                 = 1'b0;
    rf_ren_a_o            = 1'b0;
    rf_ren_b_o            = 1'b0;

    csr_access_o          = 1'b0;
    csr_illegal           = 1'b0;
    csr_op                = CSR_OP_READ;

    data_we_o             = 1'b0;
    data_type_o           = 2'b00;
    data_sign_extension_o = 1'b0;
    data_req_o            = 1'b0;

    illegal_insn          = 1'b0;
    ebrk_insn_o           = 1'b0;
    mret_insn_o           = 1'b0;
    dret_insn_o           = 1'b0;
    ecall_insn_o          = 1'b0;
    wfi_insn_o            = 1'b0;

    opcode                = opcode_e'(instr[6:0]);

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
            unique case (instr[31:27])
              5'b0_0000: illegal_insn = (instr[26:25] == 2'b00) ? 1'b0 : 1'b1;        // slli
              5'b0_0100: begin                                                        // sloi
                illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
              end
              5'b0_1001,                                                              // bclri
              5'b0_0101,                                                              // bseti
              5'b0_1101: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;           // binvi
              5'b0_0001: begin
                if (instr[26] == 1'b0) begin                                          // shfl
                  illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                end else begin
                  illegal_insn = 1'b1;
                end
              end
              5'b0_1100: begin
                unique case(instr[26:20])
                  7'b000_0000,                                                         // clz
                  7'b000_0001,                                                         // ctz
                  7'b000_0010,                                                         // cpop
                  7'b000_0100,                                                         // sext.b
                  7'b000_0101: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;      // sext.h
                  7'b001_0000,                                                         // crc32.b
                  7'b001_0001,                                                         // crc32.h
                  7'b001_0010,                                                         // crc32.w
                  7'b001_1000,                                                         // crc32c.b
                  7'b001_1001,                                                         // crc32c.h
                  7'b001_1010: begin                                                   // crc32c.w
                    illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                  end
                  default: illegal_insn = 1'b1;
                endcase
              end
              default : illegal_insn = 1'b1;
            endcase
          end

          3'b101: begin
            if (instr[26]) begin
              illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;                       // fsri
            end else begin
              unique case (instr[31:27])
                5'b0_0000,                                                             // srli
                5'b0_1000: illegal_insn = (instr[26:25] == 2'b00) ? 1'b0 : 1'b1;       // srai

                5'b0_0100: begin                                                       // sroi
                  illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                end
                5'b0_1100,                                                             // rori
                5'b0_1001: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;          // bexti

                5'b0_1101: begin
                  if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                    illegal_insn = 1'b0;                                               // grevi
                  end else if (RV32B == RV32BBalanced) begin
                    illegal_insn = (instr[24:20] == 5'b11000) ? 1'b0 : 1'b1;           // rev8
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end
                5'b0_0101: begin
                  if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                    illegal_insn = 1'b0;                                              // gorci
                  end else if (instr[24:20] == 5'b00111) begin
                    illegal_insn = (RV32B == RV32BBalanced) ? 1'b0 : 1'b1;            // orc.b
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end
                5'b0_0001: begin
                  if (instr[26] == 1'b0) begin                                        // unshfl
                    illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end

                default: illegal_insn = 1'b1;
              endcase
            end
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        rf_ren_a_o      = 1'b1;
        rf_ren_b_o      = 1'b1;
        rf_we           = 1'b1;
        if ({instr[26], instr[13:12]} == {1'b1, 2'b01}) begin
          illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1; // cmix / cmov / fsl / fsr
        end else begin
          unique case ({instr[31:25], instr[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000},
            {7'b010_0000, 3'b000},
            {7'b000_0000, 3'b010},
            {7'b000_0000, 3'b011},
            {7'b000_0000, 3'b100},
            {7'b000_0000, 3'b110},
            {7'b000_0000, 3'b111},
            {7'b000_0000, 3'b001},
            {7'b000_0000, 3'b101},
            {7'b010_0000, 3'b101}: illegal_insn = 1'b0;

            // RV32B zba
            {7'b001_0000, 3'b010}, // sh1add
            {7'b001_0000, 3'b100}, // sh2add
            {7'b001_0000, 3'b110}, // sh3add
            // RV32B zbb
            {7'b010_0000, 3'b111}, // andn
            {7'b010_0000, 3'b110}, // orn
            {7'b010_0000, 3'b100}, // xnor
            {7'b011_0000, 3'b001}, // rol
            {7'b011_0000, 3'b101}, // ror
            {7'b000_0101, 3'b100}, // min
            {7'b000_0101, 3'b110}, // max
            {7'b000_0101, 3'b101}, // minu
            {7'b000_0101, 3'b111}, // maxu
            {7'b000_0100, 3'b100}, // pack
            {7'b010_0100, 3'b100}, // packu
            {7'b000_0100, 3'b111}, // packh
            // RV32B zbs
            {7'b010_0100, 3'b001}, // bclr
            {7'b001_0100, 3'b001}, // bset
            {7'b011_0100, 3'b001}, // binv
            {7'b010_0100, 3'b101}, // bext
            // RV32B zbf
            {7'b010_0100, 3'b111}: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1; // bfp
            // RV32B zbp
            {7'b011_0100, 3'b101}, // grev
            {7'b001_0100, 3'b101}, // gorc
            {7'b000_0100, 3'b001}, // shfl
            {7'b000_0100, 3'b101}, // unshfl
            {7'b001_0100, 3'b010}, // xperm.n
            {7'b001_0100, 3'b100}, // xperm.b
            {7'b001_0100, 3'b110}, // xperm.h
            {7'b001_0000, 3'b001}, // slo
            {7'b001_0000, 3'b101}, // sro
            // RV32B zbc
            {7'b000_0101, 3'b001}, // clmul
            {7'b000_0101, 3'b010}, // clmulr
            {7'b000_0101, 3'b011}: begin // clmulh
              illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
            end
            // RV32B zbe
            {7'b010_0100, 3'b110}, // bdecompress
            {7'b000_0100, 3'b110}: illegal_insn = (RV32B == RV32BFull) ? 1'b0 : 1'b1; // bcompress

            // RV32M instructions
            {7'b000_0001, 3'b000}: begin // mul
              multdiv_operator_o    = MD_OP_MULL;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b001}: begin // mulh
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b010}: begin // mulhsu
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b01;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b011}: begin // mulhu
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b100}: begin // div
              multdiv_operator_o    = MD_OP_DIV;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b101}: begin // divu
              multdiv_operator_o    = MD_OP_DIV;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b110}: begin // rem
              multdiv_operator_o    = MD_OP_REM;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b111}: begin // remu
              multdiv_operator_o    = MD_OP_REM;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
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
        unique case (instr[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
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
          if (instr_rs1 != 5'b0 || instr_rd != 5'b0) begin
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


    opcode_alu         = opcode_e'(instr_alu[6:0]);

    use_rs3_d          = 1'b0;
    alu_multicycle_o   = 1'b0;
    mult_sel_o         = 1'b0;
    div_sel_o          = 1'b0;

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
          bt_a_mux_sel_o = OP_A_CURRPC;
          // Not-taken branch will jump to next instruction (used in secure mode)
          bt_b_mux_sel_o = branch_taken_i ? IMM_B_B : IMM_B_INCR_PC;
        end

        // Without branch target ALU, a branch is a two-stage operation using the Main ALU in both
        // stages
        if (instr_first_cycle_i) begin
          // First evaluate the branch condition
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_REG_B;
        end else if (!BranchTargetALU) begin
          // Then calculate jump target
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          // Not-taken branch will jump to next instruction (used in secure mode)
          imm_b_mux_sel_o     = branch_taken_i ? IMM_B_B : IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
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
            if (RV32B != RV32BNone) begin
              unique case (instr_alu[31:27])
                5'b0_0000: alu_operator_o = ALU_SLL;    // Shift Left Logical by Immediate
                // Shift Left Ones by Immediate
                5'b0_0100: begin
                  if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SLO;
                end
                5'b0_1001: alu_operator_o = ALU_BCLR; // Clear bit specified by immediate
                5'b0_0101: alu_operator_o = ALU_BSET; // Set bit specified by immediate
                5'b0_1101: alu_operator_o = ALU_BINV; // Invert bit specified by immediate.
                // Shuffle with Immediate Control Value
                5'b0_0001: if (instr_alu[26] == 0) alu_operator_o = ALU_SHFL;
                5'b0_1100: begin
                  unique case (instr_alu[26:20])
                    7'b000_0000: alu_operator_o = ALU_CLZ;   // clz
                    7'b000_0001: alu_operator_o = ALU_CTZ;   // ctz
                    7'b000_0010: alu_operator_o = ALU_CPOP;  // cpop
                    7'b000_0100: alu_operator_o = ALU_SEXTB; // sext.b
                    7'b000_0101: alu_operator_o = ALU_SEXTH; // sext.h
                    7'b001_0000: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_B;  // crc32.b
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_0001: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_H;  // crc32.h
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_0010: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_W;  // crc32.w
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1000: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_B; // crc32c.b
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1001: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_H; // crc32c.h
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1010: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_W; // crc32c.w
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    default: ;
                  endcase
                end

                default: ;
              endcase
            end else begin
              alu_operator_o = ALU_SLL; // Shift Left Logical by Immediate
            end
          end

          3'b101: begin
            if (RV32B != RV32BNone) begin
              if (instr_alu[26] == 1'b1) begin
                alu_operator_o = ALU_FSR;
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end else begin
                unique case (instr_alu[31:27])
                  5'b0_0000: alu_operator_o = ALU_SRL;   // Shift Right Logical by Immediate
                  5'b0_1000: alu_operator_o = ALU_SRA;   // Shift Right Arithmetically by Immediate
                  // Shift Right Ones by Immediate
                  5'b0_0100: begin
                    if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SRO;
                  end
                  5'b0_1001: alu_operator_o = ALU_BEXT;  // Extract bit specified by immediate.
                  5'b0_1100: begin
                    alu_operator_o = ALU_ROR;            // Rotate Right by Immediate
                    alu_multicycle_o = 1'b1;
                  end
                  5'b0_1101: alu_operator_o = ALU_GREV;  // General Reverse with Imm Control Val
                  5'b0_0101: alu_operator_o = ALU_GORC;  // General Or-combine with Imm Control Val
                  // Unshuffle with Immediate Control Value
                  5'b0_0001: begin
                    if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                      if (instr_alu[26] == 1'b0) alu_operator_o = ALU_UNSHFL;
                    end
                  end
                  default: ;
                endcase
              end

            end else begin
              if (instr_alu[31:27] == 5'b0_0000) begin
                alu_operator_o = ALU_SRL;               // Shift Right Logical by Immediate
              end else if (instr_alu[31:27] == 5'b0_1000) begin
                alu_operator_o = ALU_SRA;               // Shift Right Arithmetically by Immediate
              end
            end
          end

          default: ;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;

        if (instr_alu[26]) begin
          if (RV32B != RV32BNone) begin
            unique case ({instr_alu[26:25], instr_alu[14:12]})
              {2'b11, 3'b001}: begin
                alu_operator_o   = ALU_CMIX; // cmix
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b11, 3'b101}: begin
                alu_operator_o   = ALU_CMOV; // cmov
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b10, 3'b001}: begin
                alu_operator_o   = ALU_FSL;  // fsl
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b10, 3'b101}: begin
                alu_operator_o   = ALU_FSR;  // fsr
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              default: ;
            endcase
          end
        end else begin
          unique case ({instr_alu[31:25], instr_alu[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
            {7'b010_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
            {7'b000_0000, 3'b010}: alu_operator_o = ALU_SLT;   // Set Lower Than
            {7'b000_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
            {7'b000_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
            {7'b000_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
            {7'b000_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
            {7'b000_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
            {7'b000_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
            {7'b010_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

            // RV32B ALU Operations
            {7'b011_0000, 3'b001}: begin
              if (RV32B != RV32BNone) begin
                alu_operator_o = ALU_ROL;
                alu_multicycle_o = 1'b1;
              end
            end
            {7'b011_0000, 3'b101}: begin
              if (RV32B != RV32BNone) begin
                alu_operator_o = ALU_ROR;
                alu_multicycle_o = 1'b1;
              end
            end

            {7'b000_0101, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_MIN;
            {7'b000_0101, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_MAX;
            {7'b000_0101, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_MINU;
            {7'b000_0101, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_MAXU;

            {7'b000_0100, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACK;
            {7'b010_0100, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACKU;
            {7'b000_0100, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACKH;

            {7'b010_0000, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_XNOR;
            {7'b010_0000, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_ORN;
            {7'b010_0000, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_ANDN;

            // RV32B zba
            {7'b001_0000, 3'b010}: if (RV32B != RV32BNone) alu_operator_o = ALU_SH1ADD;
            {7'b001_0000, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_SH2ADD;
            {7'b001_0000, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_SH3ADD;

            // RV32B zbs
            {7'b010_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_BCLR;
            {7'b001_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_BSET;
            {7'b011_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_BINV;
            {7'b010_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_BEXT;

            // RV32B zbf
            {7'b010_0100, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_BFP;

            // RV32B zbp
            {7'b011_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_GREV;
            {7'b001_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_GORC;
            {7'b000_0100, 3'b001}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SHFL;
            end
            {7'b000_0100, 3'b101}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_UNSHFL;
            end
            {7'b001_0100, 3'b010}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_XPERM_N;
            end
            {7'b001_0100, 3'b100}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_XPERM_B;
            end
            {7'b001_0100, 3'b110}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_XPERM_H;
            end
            {7'b001_0000, 3'b001}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SLO;
            end
            {7'b001_0000, 3'b101}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SRO;
            end

            // RV32B zbc
            {7'b000_0101, 3'b001}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_CLMUL;
            end
            {7'b000_0101, 3'b010}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_CLMULR;
            end
            {7'b000_0101, 3'b011}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_CLMULH;
            end

            // RV32B zbe
            {7'b010_0100, 3'b110}: begin
              if (RV32B == RV32BFull) begin
                alu_operator_o = ALU_BDECOMPRESS;
                alu_multicycle_o = 1'b1;
              end
            end
            {7'b000_0100, 3'b110}: begin
              if (RV32B == RV32BFull) begin
                alu_operator_o = ALU_BCOMPRESS;
                alu_multicycle_o = 1'b1;
              end
            end

            // RV32M instructions, all use the same ALU operation
            {7'b000_0001, 3'b000}: begin // mul
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b001}: begin // mulh
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b010}: begin // mulhsu
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b011}: begin // mulhu
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b100}: begin // div
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b101}: begin // divu
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b110}: begin // rem
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b111}: begin // remu
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end

            default: ;
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        unique case (instr_alu[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
            alu_operator_o     = ALU_ADD; // nop
            alu_op_a_mux_sel_o = OP_A_REG_A;
            alu_op_b_mux_sel_o = OP_B_IMM;
          end
          3'b001: begin
            // FENCE.I will flush the IF stage, prefetch buffer and ICache if present.
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

  // do not enable multdiv in case of illegal instruction exceptions
  assign mult_en_o = illegal_insn ? 1'b0 : mult_sel_o;
  assign div_en_o  = illegal_insn ? 1'b0 : div_sel_o;

  // make sure instructions accessing non-available registers in RV32E cause illegal
  // instruction exceptions
  assign illegal_insn_o = illegal_insn | illegal_reg_rv32e;

  // do not propgate regfile write enable if non-available registers are accessed in RV32E
  assign rf_we_o = rf_we & ~illegal_reg_rv32e;

  // Not all bits are used
  assign unused_instr_alu = {instr_alu[19:15],instr_alu[11:7]};

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexRegImmAluOpKnown, (opcode == OPCODE_OP_IMM) |->
      !$isunknown(instr[14:12]))
endmodule // controller
