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

  output insn_dec_base_t   insn_dec_base_o,
  output insn_dec_bignum_t insn_dec_bignum_o,
  output insn_dec_shared_t insn_dec_shared_o
);

  logic        illegal_insn;
  logic        rf_we_base;
  logic        rf_we_bignum;

  logic [31:0] insn;
  logic [31:0] insn_alu;

  // Source/Destination register instruction index
  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rd;

  insn_opcode_e     opcode;
  insn_opcode_e     opcode_alu;

  assign insn     = insn_fetch_resp_data_i;
  assign insn_alu = insn_fetch_resp_data_i;

  logic unused_insn_alu_bits;
  assign unused_insn_alu_bits = (|insn_alu[11:7]) | (|insn_alu[24:15]);

  //////////////////////////////////////
  // Register and immediate selection //
  //////////////////////////////////////
  imm_b_sel_base_e   imm_b_mux_sel_base; // immediate selection for operand b in base ISA
  shamt_sel_bignum_e shift_amt_mux_sel_bignum; // shift amount selection in bignum ISA

  // Immediates from RV32I encoding
  logic [31:0] imm_i_type_base;
  logic [31:0] imm_s_type_base;
  logic [31:0] imm_b_type_base;
  logic [31:0] imm_u_type_base;
  logic [31:0] imm_j_type_base;

  // Immediates specific to OTBN encoding
  logic [31:0] imm_l_type_base;
  logic [31:0] imm_x_type_base;

  alu_op_base_e   alu_operator_base;      // ALU operation selection for base ISA
  alu_op_bignum_e alu_operator_bignum;    // ALU operation selection for bignum ISA

  op_a_sel_e alu_op_a_mux_sel_base; // operand a selection for base ISA: reg value, PC or zero
  op_b_sel_e alu_op_b_mux_sel_base; // operand b selection for base ISA: reg value or immediate

  op_b_sel_e alu_op_b_mux_sel_bignum; // operand b selection for bignum ISA: reg value or immediate

  comparison_op_base_e comparison_operator_base;


  logic [1:0] mac_op_a_qw_sel_bignum;
  logic [1:0] mac_op_b_qw_sel_bignum;
  logic       mac_wr_hw_sel_upper_bignum;
  logic [1:0] mac_pre_acc_shift_bignum;
  logic       mac_zero_acc_bignum;
  logic       mac_shift_out_bignum;
  logic       mac_en_bignum;

  logic rf_ren_a_base;
  logic rf_ren_b_base;

  logic rf_ren_a_bignum;
  logic rf_ren_b_bignum;

  logic rf_a_indirect_bignum;
  logic rf_b_indirect_bignum;
  logic rf_d_indirect_bignum;

  // immediate extraction and sign extension
  assign imm_i_type_base = {{20{insn[31]}}, insn[31:20]};
  assign imm_s_type_base = {{20{insn[31]}}, insn[31:25], insn[11:7]};
  assign imm_b_type_base = {{19{insn[31]}}, insn[31], insn[7], insn[30:25], insn[11:8], 1'b0};
  assign imm_u_type_base = {insn[31:12], 12'b0};
  assign imm_j_type_base = {{12{insn[31]}}, insn[19:12], insn[20], insn[30:21], 1'b0};
  // l type immediate is for the loop count in the LOOPI instruction and is not from the RISC-V ISA
  assign imm_l_type_base = {22'b0, insn[19:15], insn[11:7]};
  // x type immediate is for BN.LID/BN.SID instructions and is not from the RISC-V ISA
  assign imm_x_type_base = {{17{insn[11]}}, insn[11:9], insn[31:25], 5'b0};

  logic [WLEN-1:0] imm_i_type_bignum;

  assign imm_i_type_bignum = {{(WLEN-10){1'b0}}, insn[29:20]};

  // Shift amount for ALU instructions other than BN.RSHI
  logic [$clog2(WLEN)-1:0] shift_amt_a_type_bignum;
  // Shift amount for BN.RSHI
  logic [$clog2(WLEN)-1:0] shift_amt_s_type_bignum;

  assign shift_amt_a_type_bignum = {insn[29:25], 3'b0};
  assign shift_amt_s_type_bignum = {insn[31:25], insn[14]};

  logic alu_shift_right_bignum;

  assign alu_shift_right_bignum = insn[30];

  flag_group_t alu_flag_group_bignum;

  assign alu_flag_group_bignum = insn[31];

  flag_e alu_sel_flag_bignum;

  assign alu_sel_flag_bignum = flag_e'(insn[26:25]);

  logic alu_flag_en_bignum;
  logic mac_flag_en_bignum;

  // source registers
  assign insn_rs1 = insn[19:15];
  assign insn_rs2 = insn[24:20];

  // destination register
  assign insn_rd = insn[11:7];

  insn_subset_e insn_subset;
  rf_wd_sel_e rf_wdata_sel_base;
  rf_wd_sel_e rf_wdata_sel_bignum;

  logic [11:0] loop_bodysize_base;
  logic        loop_immediate_base;

  assign loop_bodysize_base  = insn[31:20];
  assign loop_immediate_base = insn[12];

  assign mac_op_a_qw_sel_bignum     = insn[26:25];
  assign mac_op_b_qw_sel_bignum     = insn[28:27];
  assign mac_wr_hw_sel_upper_bignum = insn[29];
  assign mac_pre_acc_shift_bignum   = insn[14:13];
  assign mac_zero_acc_bignum        = insn[12];
  assign mac_shift_out_bignum       = insn[30];

  logic d_inc_bignum;
  logic a_inc_bignum;
  logic a_wlen_word_inc_bignum;
  logic b_inc_bignum;

  logic sel_insn_bignum;

  logic ecall_insn;
  logic ld_insn;
  logic st_insn;
  logic branch_insn;
  logic jump_insn;
  logic loop_insn;
  logic ispr_rd_insn;
  logic ispr_wr_insn;
  logic ispr_rs_insn;

  // Reduced main ALU immediate MUX for Operand B
  logic [31:0] imm_b_base;
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel_base)
      ImmBaseBI: imm_b_base = imm_i_type_base;
      ImmBaseBS: imm_b_base = imm_s_type_base;
      ImmBaseBU: imm_b_base = imm_u_type_base;
      ImmBaseBB: imm_b_base = imm_b_type_base;
      ImmBaseBJ: imm_b_base = imm_j_type_base;
      ImmBaseBL: imm_b_base = imm_l_type_base;
      ImmBaseBX: imm_b_base = imm_x_type_base;
      default:   imm_b_base = imm_i_type_base;
    endcase
  end

  logic [$clog2(WLEN)-1:0] alu_shift_amt_bignum;
  always_comb begin
    unique case (shift_amt_mux_sel_bignum)
      ShamtSelBignumA:    alu_shift_amt_bignum = shift_amt_a_type_bignum;
      ShamtSelBignumS:    alu_shift_amt_bignum = shift_amt_s_type_bignum;
      ShamtSelBignumZero: alu_shift_amt_bignum = '0;
      default:            alu_shift_amt_bignum = shift_amt_a_type_bignum;
    endcase
  end

  assign insn_valid_o   = insn_fetch_resp_valid_i & ~illegal_insn;
  assign insn_illegal_o = insn_fetch_resp_valid_i & illegal_insn;

  assign insn_dec_base_o = '{
    a:              insn_rs1,
    b:              insn_rs2,
    d:              insn_rd,
    i:              imm_b_base,
    alu_op:         alu_operator_base,
    comparison_op:  comparison_operator_base,
    op_a_sel:       alu_op_a_mux_sel_base,
    op_b_sel:       alu_op_b_mux_sel_base,
    rf_we:          rf_we_base,
    rf_wdata_sel:   rf_wdata_sel_base,
    rf_ren_a:       rf_ren_a_base,
    rf_ren_b:       rf_ren_b_base,
    loop_bodysize:  loop_bodysize_base,
    loop_immediate: loop_immediate_base
  };

  assign insn_dec_bignum_o = '{
    a:                   insn_rs1,
    b:                   insn_rs2,
    d:                   insn_rd,
    i:                   imm_i_type_bignum,
    rf_a_indirect:       rf_a_indirect_bignum,
    rf_b_indirect:       rf_b_indirect_bignum,
    rf_d_indirect:       rf_d_indirect_bignum,
    d_inc:               d_inc_bignum,
    a_inc:               a_inc_bignum,
    a_wlen_word_inc:     a_wlen_word_inc_bignum,
    b_inc:               b_inc_bignum,
    alu_shift_amt:       alu_shift_amt_bignum,
    alu_shift_right:     alu_shift_right_bignum,
    alu_flag_group:      alu_flag_group_bignum,
    alu_sel_flag:        alu_sel_flag_bignum,
    alu_flag_en:         alu_flag_en_bignum,
    mac_flag_en:         mac_flag_en_bignum,
    alu_op:              alu_operator_bignum,
    alu_op_b_sel:        alu_op_b_mux_sel_bignum,
    mac_op_a_qw_sel:     mac_op_a_qw_sel_bignum,
    mac_op_b_qw_sel:     mac_op_b_qw_sel_bignum,
    mac_wr_hw_sel_upper: mac_wr_hw_sel_upper_bignum,
    mac_pre_acc_shift:   mac_pre_acc_shift_bignum,
    mac_zero_acc:        mac_zero_acc_bignum,
    mac_shift_out:       mac_shift_out_bignum,
    mac_en:              mac_en_bignum,
    rf_we:               rf_we_bignum,
    rf_wdata_sel:        rf_wdata_sel_bignum,
    rf_ren_a:            rf_ren_a_bignum,
    rf_ren_b:            rf_ren_b_bignum,
    sel_insn:            sel_insn_bignum
  };

  assign insn_dec_shared_o = '{
    subset:        insn_subset,
    ecall_insn:    ecall_insn,
    ld_insn:       ld_insn,
    st_insn:       st_insn,
    branch_insn:   branch_insn,
    jump_insn:     jump_insn,
    loop_insn:     loop_insn,
    ispr_rd_insn:  ispr_rd_insn,
    ispr_wr_insn:  ispr_wr_insn,
    ispr_rs_insn:  ispr_rs_insn
  };

  /////////////
  // Decoder //
  /////////////

  always_comb begin
    insn_subset            = InsnSubsetBase;

    rf_wdata_sel_base      = RfWdSelEx;
    rf_we_base             = 1'b0;

    rf_wdata_sel_bignum    = RfWdSelEx;
    rf_we_bignum           = 1'b0;

    rf_ren_a_base          = 1'b0;
    rf_ren_b_base          = 1'b0;
    rf_ren_a_bignum        = 1'b0;
    rf_ren_b_bignum        = 1'b0;
    mac_en_bignum          = 1'b0;

    rf_a_indirect_bignum   = 1'b0;
    rf_b_indirect_bignum   = 1'b0;
    rf_d_indirect_bignum   = 1'b0;

    d_inc_bignum           = 1'b0;
    a_inc_bignum           = 1'b0;
    a_wlen_word_inc_bignum = 1'b0;
    b_inc_bignum           = 1'b0;

    illegal_insn           = 1'b0;
    ecall_insn             = 1'b0;
    ld_insn                = 1'b0;
    st_insn                = 1'b0;
    branch_insn            = 1'b0;
    jump_insn              = 1'b0;
    loop_insn              = 1'b0;
    ispr_rd_insn           = 1'b0;
    ispr_wr_insn           = 1'b0;
    ispr_rs_insn           = 1'b0;

    sel_insn_bignum        = 1'b0;

    opcode                 = insn_opcode_e'(insn[6:0]);

    unique case (opcode)
      //////////////
      // Base ALU //
      //////////////

      InsnOpcodeBaseLui: begin  // Load Upper Immediate
        insn_subset = InsnSubsetBase;
        rf_we_base  = 1'b1;
      end

      InsnOpcodeBaseOpImm: begin  // Register-Immediate ALU Operations
        insn_subset   = InsnSubsetBase;
        rf_ren_a_base = 1'b1;
        rf_we_base    = 1'b1;

        unique case (insn[14:12])
          3'b000,  // addi
          3'b100,  // xori
          3'b110,  // ori
          3'b111:  // andi
            illegal_insn = 1'b0;

          3'b001: begin
            unique case (insn[31:25])
              7'b0000000: illegal_insn = 1'b0;  // slli
              default: illegal_insn = 1'b1;
            endcase
          end

          3'b101: begin
            unique case (insn[31:25])
              7'b0000000,                      // srli
              7'b0100000: illegal_insn = 1'b0; // srai

              default: illegal_insn = 1'b1;
            endcase
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      InsnOpcodeBaseOp: begin  // Register-Register ALU operation
        insn_subset   = InsnSubsetBase;
        rf_ren_a_base = 1'b1;
        rf_ren_b_base = 1'b1;
        rf_we_base    = 1'b1;
        // Look at the funct7 and funct3 fields.
        unique case ({insn[31:25], insn[14:12]})
          {7'b000_0000, 3'b000},  // ADD
          {7'b010_0000, 3'b000},  // SUB
          {7'b000_0000, 3'b100},  // XOR
          {7'b000_0000, 3'b110},  // OR
          {7'b000_0000, 3'b111},  // AND
          {7'b000_0000, 3'b001},  // SLL
          {7'b000_0000, 3'b101},  // SRL
          {7'b010_0000, 3'b101}:  // SRA
            illegal_insn = 1'b0;

          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      ///////////////////////
      // Base Loads/Stores //
      ///////////////////////

      InsnOpcodeBaseLoad: begin
        insn_subset       = InsnSubsetBase;
        ld_insn           = 1'b1;
        rf_ren_a_base     = 1'b1;
        rf_we_base        = 1'b1;
        rf_wdata_sel_base = RfWdSelLsu;

        if (insn[14:12] != 3'b010) begin
          illegal_insn = 1'b1;
        end
      end

      InsnOpcodeBaseStore: begin
        insn_subset   = InsnSubsetBase;
        st_insn       = 1'b1;
        rf_ren_a_base = 1'b1;
        rf_ren_b_base = 1'b1;

        if (insn[14:12] != 3'b010) begin
          illegal_insn = 1'b1;
        end
      end

      //////////////////////
      // Base Branch/Jump //
      //////////////////////

      InsnOpcodeBaseBranch: begin
        insn_subset   = InsnSubsetBase;
        branch_insn   = 1'b1;
        rf_ren_a_base = 1'b1;
        rf_ren_b_base = 1'b1;

        // Only EQ & NE comparisons allowed
        if (insn[14:13] != 2'b00) begin
          illegal_insn = 1'b1;
        end
      end

      InsnOpcodeBaseJal: begin
        insn_subset       = InsnSubsetBase;
        jump_insn         = 1'b1;
        rf_we_base        = 1'b1;
        rf_wdata_sel_base = RfWdSelNextPc;
      end

      InsnOpcodeBaseJalr: begin
        insn_subset       = InsnSubsetBase;
        jump_insn         = 1'b1;
        rf_ren_a_base     = 1'b1;
        rf_we_base        = 1'b1;
        rf_wdata_sel_base = RfWdSelNextPc;

        if (insn[14:12] != 3'b000) begin
          illegal_insn = 1'b1;
        end
      end

      //////////////////
      // Base Special //
      //////////////////

      InsnOpcodeBaseSystem: begin
        insn_subset = InsnSubsetBase;
        if (insn[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          unique case (insn[31:20])
            12'h000:  // ECALL
              ecall_insn = 1'b1;

            default:
              illegal_insn = 1'b1;
          endcase

          // rs1 and rd must be 0
          if (insn_rs1 != 5'b0 || insn_rd != 5'b0) begin
            illegal_insn = 1'b1;
          end
        end else begin
          rf_we_base        = 1'b1;
          rf_wdata_sel_base = RfWdSelIspr;
          rf_ren_a_base     = 1'b1;

          if (insn[14:12] == 3'b001) begin
            // No read if destination is x0 unless read is to flags CSR. Both flag groups are in
            // a single ISPR so to write one group the other must be read to write it back
            // unchanged.
            ispr_rd_insn = (insn_rd != 5'b0)            |
                           (imm_b_base[11:0] == CsrFg0) |
                           (imm_b_base[11:0] == CsrFg1);
            ispr_wr_insn = 1'b1;
          end else if (insn[14:12] == 3'b010) begin
            // Read and set if source register isn't x0, otherwise read only
            if (insn_rs1 != 5'b0) begin
              ispr_rs_insn = 1'b1;
            end else begin
              ispr_rd_insn = 1'b1;
            end
          end else begin
            illegal_insn = 1'b1;
          end
        end
      end

      ////////////////
      // Bignum ALU //
      ////////////////

      InsnOpcodeBignumArith: begin
        insn_subset     = InsnSubsetBignum;
        rf_we_bignum    = 1'b1;
        rf_ren_a_bignum = 1'b1;

        if (insn[14:12] != 3'b100) begin
          // All Alu instructions other than BN.ADDI/BN.SUBI
          rf_ren_b_bignum = 1'b1;
        end

        unique case(insn[14:12])
          3'b110,
          3'b111: illegal_insn = 1'b1;
          default: ;
        endcase
      end

      ///////////////////////////////////////
      // Bignum logical/BN.RSHI/LOOP/LOOPI //
      ///////////////////////////////////////

      InsnOpcodeBignumBaseMisc: begin
        unique case (insn[14:12])
          3'b000, 3'b001: begin  // LOOP[I]
            insn_subset   = InsnSubsetBase;
            rf_ren_a_base = ~insn[12];
            loop_insn     = 1'b1;
          end
          3'b010, 3'b011, 3'b100, 3'b110, 3'b111: begin  // BN.RHSI/BN.AND/BN.OR/BN.XOR
            insn_subset     = InsnSubsetBignum;
            rf_we_bignum    = 1'b1;
            rf_ren_a_bignum = 1'b1;
            rf_ren_b_bignum = 1'b1;
          end
          3'b101: begin  // BN.NOT
            insn_subset     = InsnSubsetBignum;
            rf_we_bignum    = 1'b1;
            rf_ren_b_bignum = 1'b1;
          end
          default: illegal_insn = 1'b1;
        endcase
      end

      ///////////////////////////////////////////////
      // Bignum Misc WSR/LID/SID/MOV[R]/CMP[B]/SEL //
      ///////////////////////////////////////////////

      InsnOpcodeBignumMisc: begin
        insn_subset = InsnSubsetBignum;

        unique case (insn[14:12])
          3'b000: begin  // BN.SEL
            rf_we_bignum        = 1'b1;
            rf_ren_a_bignum     = 1'b1;
            rf_ren_b_bignum     = 1'b1;
            rf_wdata_sel_bignum = RfWdSelMovSel;
            sel_insn_bignum     = 1'b1;
          end
          3'b011, 3'b001: begin  // BN.CMP[B]
            rf_ren_a_bignum = 1'b1;
            rf_ren_b_bignum = 1'b1;
          end
          3'b100: begin  // BN.LID
            ld_insn              = 1'b1;
            rf_we_bignum         = 1'b1;
            rf_ren_a_base        = 1'b1;
            rf_ren_b_base        = 1'b1;
            rf_wdata_sel_bignum  = RfWdSelLsu;
            rf_d_indirect_bignum = 1'b1;

            if (insn[8]) begin
              a_wlen_word_inc_bignum = 1'b1;
              rf_we_base             = 1'b1;
              rf_wdata_sel_base      = RfWdSelIncr;
            end

            if (insn[7]) begin
              d_inc_bignum      = 1'b1;
              rf_we_base        = 1'b1;
              rf_wdata_sel_base = RfWdSelIncr;
            end

            if (insn[8] & insn[7]) begin
              // Avoid violating unique constraint for inc selection mux on an illegal instruction
              a_wlen_word_inc_bignum = 1'b0;
              d_inc_bignum           = 1'b0;
              illegal_insn           = 1'b1;
            end
          end
          3'b101: begin  // BN.SID
            st_insn              = 1'b1;
            rf_ren_a_base        = 1'b1;
            rf_ren_b_base        = 1'b1;
            rf_ren_b_bignum      = 1'b1;
            rf_b_indirect_bignum = 1'b1;

            if (insn[8]) begin
              a_wlen_word_inc_bignum = 1'b1;
              rf_we_base             = 1'b1;
              rf_wdata_sel_base      = RfWdSelIncr;
            end

            if (insn[7]) begin
              b_inc_bignum = 1'b1;
              rf_we_base   = 1'b1;
              rf_wdata_sel_base = RfWdSelIncr;
            end

            if (insn[8] & insn[7]) begin
              // Avoid violating unique constraint for inc selection mux on an illegal instruction
              a_wlen_word_inc_bignum = 1'b0;
              b_inc_bignum           = 1'b0;
              illegal_insn           = 1'b1;
            end
          end
          3'b110: begin  // BN.MOV/BN.MOVR
            insn_subset         = InsnSubsetBignum;
            rf_we_bignum        = 1'b1;
            rf_ren_a_bignum     = 1'b1;
            rf_wdata_sel_bignum = RfWdSelMovSel;

            if (insn[31]) begin  // BN.MOVR
              rf_a_indirect_bignum = 1'b1;
              rf_d_indirect_bignum = 1'b1;
              rf_ren_a_base        = 1'b1;
              rf_ren_b_base        = 1'b1;

              if (insn[9]) begin
                a_inc_bignum      = 1'b1;
                rf_we_base        = 1'b1;
                rf_wdata_sel_base = RfWdSelIncr;
              end

              if (insn[7]) begin
                d_inc_bignum      = 1'b1;
                rf_we_base        = 1'b1;
                rf_wdata_sel_base = RfWdSelIncr;
              end

              if (insn[9] & insn[7]) begin
                // Avoid violating unique constraint for inc selection mux on an illegal instruction
                a_inc_bignum = 1'b0;
                d_inc_bignum = 1'b0;
                illegal_insn = 1'b1;
              end
            end
          end
          3'b111: begin
            if (insn[31]) begin  // BN.WSRW
              rf_ren_a_bignum = 1'b1;
              ispr_wr_insn    = 1'b1;
            end else begin  // BN.WSRR
              rf_we_bignum        = 1'b1;
              rf_wdata_sel_bignum = RfWdSelIspr;
              ispr_rd_insn        = 1'b1;
            end
          end
          default: illegal_insn = 1'b1;
        endcase
      end

      ////////////////////////////////////////////
      // BN.MULQACC/BN.MULQACC.WO/BN.MULQACC.SO //
      ////////////////////////////////////////////

      InsnOpcodeBignumMulqacc: begin
        insn_subset         = InsnSubsetBignum;
        rf_ren_a_bignum     = 1'b1;
        rf_ren_b_bignum     = 1'b1;
        rf_wdata_sel_bignum = RfWdSelMac;
        mac_en_bignum       = 1'b1;

        if (insn[30] == 1'b1 || insn[29] == 1'b1) begin  // BN.MULQACC.WO/BN.MULQACC.SO
          rf_we_bignum = 1'b1;
        end
      end

      default: illegal_insn = 1'b1;
    endcase


    // make sure illegal instructions detected in the decoder do not propagate from decoder
    // NOTE: instructions can also be detected to be illegal inside the CSRs (upon accesses with
    // insufficient privileges). These cases are not handled here.
    if (illegal_insn) begin
      rf_we_base   = 1'b0;
      rf_we_bignum = 1'b0;
    end
  end

  /////////////////////////////
  // Decoder for ALU control //
  /////////////////////////////

  always_comb begin
    alu_operator_base        = AluOpBaseAdd;
    comparison_operator_base = ComparisonOpBaseEq;

    alu_op_a_mux_sel_base    = OpASelRegister;
    alu_op_b_mux_sel_base    = OpBSelImmediate;

    imm_b_mux_sel_base       = ImmBaseBI;

    alu_operator_bignum      = AluOpBignumNone;
    alu_op_b_mux_sel_bignum  = OpBSelImmediate;

    shift_amt_mux_sel_bignum = ShamtSelBignumA;

    opcode_alu               = insn_opcode_e'(insn_alu[6:0]);

    alu_flag_en_bignum       = 1'b0;
    mac_flag_en_bignum       = 1'b0;

    unique case (opcode_alu)
      //////////////
      // Base ALU //
      //////////////

      InsnOpcodeBaseLui: begin  // Load Upper Immediate
        alu_op_a_mux_sel_base = OpASelZero;
        alu_op_b_mux_sel_base = OpBSelImmediate;
        imm_b_mux_sel_base    = ImmBaseBU;
        alu_operator_base     = AluOpBaseAdd;
      end

      InsnOpcodeBaseOpImm: begin  // Register-Immediate ALU Operations
        alu_op_a_mux_sel_base = OpASelRegister;
        alu_op_b_mux_sel_base = OpBSelImmediate;
        imm_b_mux_sel_base    = ImmBaseBI;

        unique case (insn_alu[14:12])
          3'b000: alu_operator_base = AluOpBaseAdd;  // Add Immediate
          3'b100: alu_operator_base = AluOpBaseXor;  // Exclusive Or with Immediate
          3'b110: alu_operator_base = AluOpBaseOr;   // Or with Immediate
          3'b111: alu_operator_base = AluOpBaseAnd;  // And with Immediate

          3'b001: begin
            alu_operator_base = AluOpBaseSll;  // Shift Left Logical by Immediate
          end

          3'b101: begin
            if (insn_alu[31:27] == 5'b0_0000) begin
              alu_operator_base = AluOpBaseSrl;  // Shift Right Logical by Immediate
            end else if (insn_alu[31:27] == 5'b0_1000) begin
              alu_operator_base = AluOpBaseSra;  // Shift Right Arithmetically by Immediate
            end
          end

          default: ;
        endcase
      end

      InsnOpcodeBaseOp: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_base = OpASelRegister;
        alu_op_b_mux_sel_base = OpBSelRegister;

        if (!insn_alu[26]) begin
          unique case ({insn_alu[31:25], insn_alu[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000}: alu_operator_base = AluOpBaseAdd;   // Add
            {7'b010_0000, 3'b000}: alu_operator_base = AluOpBaseSub;   // Sub
            {7'b000_0000, 3'b100}: alu_operator_base = AluOpBaseXor;   // Xor
            {7'b000_0000, 3'b110}: alu_operator_base = AluOpBaseOr;    // Or
            {7'b000_0000, 3'b111}: alu_operator_base = AluOpBaseAnd;   // And
            {7'b000_0000, 3'b001}: alu_operator_base = AluOpBaseSll;   // Shift Left Logical
            {7'b000_0000, 3'b101}: alu_operator_base = AluOpBaseSrl;   // Shift Right Logical
            {7'b010_0000, 3'b101}: alu_operator_base = AluOpBaseSra;   // Shift Right Arithmetic
            default: ;
          endcase
        end
      end

      ///////////////////////
      // Base Loads/Stores //
      ///////////////////////

      InsnOpcodeBaseLoad: begin
        alu_op_a_mux_sel_base = OpASelRegister;
        alu_op_b_mux_sel_base = OpBSelImmediate;
        alu_operator_base     = AluOpBaseAdd;
        imm_b_mux_sel_base    = ImmBaseBI;
      end

      InsnOpcodeBaseStore: begin
        alu_op_a_mux_sel_base = OpASelRegister;
        alu_op_b_mux_sel_base = OpBSelImmediate;
        alu_operator_base     = AluOpBaseAdd;
        imm_b_mux_sel_base    = ImmBaseBS;
      end

      //////////////////////
      // Base Branch/Jump //
      //////////////////////

      InsnOpcodeBaseBranch: begin
        alu_op_a_mux_sel_base    = OpASelCurrPc;
        alu_op_b_mux_sel_base    = OpBSelImmediate;
        alu_operator_base        = AluOpBaseAdd;
        imm_b_mux_sel_base       = ImmBaseBB;
        comparison_operator_base = insn_alu[12] ? ComparisonOpBaseNeq : ComparisonOpBaseEq;
      end

      InsnOpcodeBaseJal: begin
        alu_op_a_mux_sel_base = OpASelCurrPc;
        alu_op_b_mux_sel_base = OpBSelImmediate;
        alu_operator_base     = AluOpBaseAdd;
        imm_b_mux_sel_base    = ImmBaseBJ;
      end

      InsnOpcodeBaseJalr: begin
        alu_op_a_mux_sel_base = OpASelRegister;
        alu_op_b_mux_sel_base = OpBSelImmediate;
        alu_operator_base     = AluOpBaseAdd;
        imm_b_mux_sel_base    = ImmBaseBI;
      end

      //////////////////
      // Base Special //
      //////////////////

      InsnOpcodeBaseSystem: begin
        // The only instructions with System opcode that care about operands are CSR access
        alu_op_a_mux_sel_base = OpASelRegister;
        imm_b_mux_sel_base    = ImmBaseBI;
      end

      ////////////////
      // Bignum ALU //
      ////////////////

      InsnOpcodeBignumArith: begin
        alu_flag_en_bignum = 1'b1;

        unique case (insn_alu[14:12])
          3'b000: alu_operator_bignum = AluOpBignumAdd;
          3'b001: alu_operator_bignum = AluOpBignumSub;
          3'b010: alu_operator_bignum = AluOpBignumAddc;
          3'b011: alu_operator_bignum = AluOpBignumSubb;
          3'b100: begin
            if (insn_alu[30]) begin
              alu_operator_bignum = AluOpBignumSub;
            end else begin
              alu_operator_bignum = AluOpBignumAdd;
            end
          end
          3'b101: begin
            if (insn_alu[30]) begin
              alu_operator_bignum = AluOpBignumSubm;
            end else begin
              alu_operator_bignum = AluOpBignumAddm;
            end
          end
          default: ;
        endcase

        if (insn_alu[14:12] != 3'b100) begin
          alu_op_b_mux_sel_bignum  = OpBSelRegister;
          shift_amt_mux_sel_bignum = ShamtSelBignumA;
        end else begin
          alu_op_b_mux_sel_bignum  = OpBSelImmediate;
          shift_amt_mux_sel_bignum = ShamtSelBignumZero;
        end
      end

      ///////////////////////////////////////
      // Bignum logical/BN.RSHI/LOOP/LOOPI //
      ///////////////////////////////////////

      InsnOpcodeBignumBaseMisc: begin
        // LOOPI uses L type immediate, base immediate irrelevant for everything else
        imm_b_mux_sel_base      = ImmBaseBL;
        alu_op_b_mux_sel_bignum = OpBSelRegister;

        unique case (insn_alu[14:12])
          3'b010: begin
            shift_amt_mux_sel_bignum = ShamtSelBignumA;
            alu_operator_bignum      = AluOpBignumAnd;
            alu_flag_en_bignum       = 1'b1;
          end
          3'b100: begin
            shift_amt_mux_sel_bignum = ShamtSelBignumA;
            alu_operator_bignum      = AluOpBignumOr;
            alu_flag_en_bignum       = 1'b1;
          end
          3'b101: begin
            shift_amt_mux_sel_bignum = ShamtSelBignumA;
            alu_operator_bignum      = AluOpBignumNot;
            alu_flag_en_bignum       = 1'b1;
          end
          3'b110: begin
            shift_amt_mux_sel_bignum = ShamtSelBignumA;
            alu_operator_bignum      = AluOpBignumXor;
            alu_flag_en_bignum       = 1'b1;
          end
          3'b011,
          3'b111: begin
            shift_amt_mux_sel_bignum = ShamtSelBignumS;
            alu_operator_bignum      = AluOpBignumRshi;
          end
          default: ;
        endcase
      end

      ///////////////////////////////////////////
      // Bignum Misc LID/SID/MOV[R]/CMP[B]/SEL //
      ///////////////////////////////////////////

      InsnOpcodeBignumMisc: begin
        unique case (insn[14:12])
          3'b001: begin  // BN.CMP
            alu_operator_bignum      = AluOpBignumSub;
            alu_op_b_mux_sel_bignum  = OpBSelRegister;
            shift_amt_mux_sel_bignum = ShamtSelBignumA;
            alu_flag_en_bignum       = 1'b1;
          end
          3'b011: begin  // BN.CMPB
            alu_operator_bignum      = AluOpBignumSubb;
            alu_op_b_mux_sel_bignum  = OpBSelRegister;
            shift_amt_mux_sel_bignum = ShamtSelBignumA;
            alu_flag_en_bignum       = 1'b1;
          end
          3'b100,
          3'b101: begin  // BN.LID/BN.SID
            // Calculate memory address using base ALU
            alu_op_a_mux_sel_base = OpASelRegister;
            alu_op_b_mux_sel_base = OpBSelImmediate;
            alu_operator_base     = AluOpBaseAdd;
            imm_b_mux_sel_base    = ImmBaseBX;
          end
          default: ;
        endcase
      end

      ////////////////////////////////////////////
      // BN.MULQACC/BN.MULQACC.WO/BN.MULQACC.SO //
      ////////////////////////////////////////////

      InsnOpcodeBignumMulqacc: begin
        if (insn[30] == 1'b1 || insn[29] == 1'b1) begin  // BN.MULQACC.WO/BN.MULQACC.SO
          mac_flag_en_bignum = 1'b1;
        end
      end

      default: ;
    endcase

  end

  // clk_i and rst_ni are only used by assertions
  logic unused_clk;
  logic unused_rst_n;

  assign unused_clk   = clk_i;
  assign unused_rst_n = rst_ni;

  ////////////////
  // Assertions //
  ////////////////


  // Selectors must be known/valid.
  `ASSERT(IbexRegImmAluOpBaseKnown, (opcode == InsnOpcodeBaseOpImm) |-> !$isunknown(insn[14:12]))

  // Can only do a single inc. Selection mux in controller doesn't factor in instruction valid (to
  // ease timing), so these must always be one-hot to 0 to avoid violating unique constraint for mux
  // case statement.
  `ASSERT(BignumRegIncOnehot,
          $onehot0({a_inc_bignum, a_wlen_word_inc_bignum, b_inc_bignum, d_inc_bignum}))

  // RfWdSelIncr requires active selection
  `ASSERT(BignumRegIncReq,
          (insn_valid_o && (rf_wdata_sel_base == RfWdSelIncr))
          |->
          $onehot({a_inc_bignum, a_wlen_word_inc_bignum, b_inc_bignum, d_inc_bignum}))

  `ASSERT(BaseRenOnBignumIndirectA, insn_valid_o & rf_a_indirect_bignum |-> rf_ren_a_base)
  `ASSERT(BaseRenOnBignumIndirectB, insn_valid_o & rf_b_indirect_bignum |-> rf_ren_b_base)
  `ASSERT(BaseRenOnBignumIndirectD, insn_valid_o & rf_d_indirect_bignum |-> rf_ren_b_base)
endmodule
