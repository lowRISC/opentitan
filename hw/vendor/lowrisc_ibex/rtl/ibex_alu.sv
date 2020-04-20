// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Arithmetic logic unit
 */
module ibex_alu #(
  parameter bit RV32B = 1'b0
) (
    input  ibex_pkg::alu_op_e operator_i,
    input  logic [31:0]       operand_a_i,
    input  logic [31:0]       operand_b_i,

    input  logic              instr_first_cycle_i,

    input  logic [32:0]       multdiv_operand_a_i,
    input  logic [32:0]       multdiv_operand_b_i,

    input  logic              multdiv_sel_i,

    input  logic [31:0]       imd_val_q_i,
    output logic [31:0]       imd_val_d_o,
    output logic              imd_val_we_o,

    output logic [31:0]       adder_result_o,
    output logic [33:0]       adder_result_ext_o,

    output logic [31:0]       result_o,
    output logic              comparison_result_o,
    output logic              is_equal_result_o
);
  import ibex_pkg::*;

  logic [31:0] operand_a_rev;
  logic [32:0] operand_b_neg;

  // bit reverse operand_a for left shifts and bit counting
  for (genvar k = 0; k < 32; k++) begin : gen_rev_operand_a
    assign operand_a_rev[k] = operand_a_i[31-k];
  end

  ///////////
  // Adder //
  ///////////

  logic        adder_op_b_negate;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;

  always_comb begin
    adder_op_b_negate = 1'b0;
    unique case (operator_i)
      // Adder OPs
      ALU_SUB,

      // Comparator OPs
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU,

      // MinMax OPs (RV32B Ops)
      ALU_MIN,  ALU_MINU,
      ALU_MAX,  ALU_MAXU: adder_op_b_negate = 1'b1;

      default:;
    endcase
  end

  // prepare operand a
  assign adder_in_a    = multdiv_sel_i ? multdiv_operand_a_i : {operand_a_i,1'b1};

  // prepare operand b
  assign operand_b_neg = {operand_b_i,1'b0} ^ {33{1'b1}};
  always_comb begin
    unique case(1'b1)
      multdiv_sel_i:     adder_in_b = multdiv_operand_b_i;
      adder_op_b_negate: adder_in_b = operand_b_neg;
      default :          adder_in_b = {operand_b_i, 1'b0};
    endcase
  end

  // actual adder
  assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  assign adder_result       = adder_result_ext_o[32:1];

  assign adder_result_o     = adder_result;

  ///////////
  // Shift //
  ///////////

  // The shifter structure consists of a 33-bit shifter: 32-bit operand + 1 bit extension for
  // arithmetic shifts and one-shift support.
  // Rotations and funnel shifts are implemented as multi-cycle instructions.
  // For funnel shifs, operand_a_i is tied to rs1 in the first cycle and rs3 in the
  // second cycle. operand_b_i is always tied to rs2.
  //
  // Rotation pseudocode:
  //   shift_amt = rs2 & 31;
  //   multicycle_result = (rs1 >> shift_amt) | (rs1 << (32 - shift_amt));
  //                       ^-- cycle 0 -----^ ^-- cycle 1 --------------^
  //
  // For funnel shifts, the order of applying the shift amount or its complement is determined by
  // bit [5] of shift_amt.
  // Funnel shift Pseudocode: (fsl)
  //  shift_amt = rs2 & 63;
  //  shift_amt_compl = 32 - shift_amt[4:0]
  //  if (shift_amt >=33):
  //     multicycle_result = (rs1 >> shift_amt_cmpl[4:0]) | (rs3 << shift_amt[4:0]);
  //                         ^-- cycle 0 ---------------^ ^-- cycle 1 ------------^
  //  else if (shift_amt <= 31 && shift_amt > 0):
  //     multicycle_result = (rs1 << shift_amt[4:0]) | (rs3 >> shift_amt_compl[4:0]);
  //                         ^-- cycle 0 ----------^ ^-- cycle 1 -------------------^
  //  For shift_amt == 0, 32, both shift_amt[4:0] and shift_amt_compl[4:0] == '0.
  //  these cases need to be handled separately outside the shifting structure:
  //  else if (shift_amt == 32):
  //     multicycle_result = rs3
  //  else if (shift_amt == 0):
  //     multicycle_result = rs1.

  logic       shift_left;
  logic       shift_ones;
  logic       shift_arith;
  logic       shift_rot;
  logic       shift_funnel;
  logic       shift_none;
  logic       shift_op_rev;
  logic       shift_op_rev8;
  logic       shift_op_orc_b;
  logic [5:0] shift_amt;
  logic [5:0] shift_amt_compl; // complementary shift amount (32 - shift_amt)
  logic       shift_multicycle;

  // bit shift_amt[5]: word swap bit: only considered for FSL/FSR.
  // if set, reverse operations in first and second cycle.
  assign shift_amt[5] = operand_b_i[5] && shift_funnel;
  assign shift_amt_compl = 32 - operand_b_i[4:0];

  assign shift_amt[4:0] = instr_first_cycle_i ?
      (operand_b_i[5] && shift_funnel ? shift_amt_compl[4:0] : operand_b_i[4:0]) :
      (operand_b_i[5] && shift_funnel ? operand_b_i[4:0] : shift_amt_compl[4:0]);

  // left shift if this is:
  // * a standard left shift (slo, sll)
  // * a rol in the first cycle
  // * a ror in the second cycle
  // * fsl: without word-swap bit: first cycle, else: second cycle
  // * fsr: without word-swap bit: second cycle, else: first cycle
  always_comb begin
    unique case (operator_i)
      ALU_SLL: shift_left = 1'b1;
      ALU_SLO: shift_left = RV32B ? 1'b1 : 1'b0;
      ALU_ROL: shift_left = RV32B ? instr_first_cycle_i : 0;
      ALU_ROR: shift_left = RV32B ? !instr_first_cycle_i : 0;
      ALU_FSL: shift_left =
          RV32B ? (shift_amt[5] ? !instr_first_cycle_i : instr_first_cycle_i) : 1'b0;
      ALU_FSR: shift_left =
          RV32B ? (shift_amt[5] ? instr_first_cycle_i : !instr_first_cycle_i) : 1'b0;
      default: shift_left = 1'b0;
    endcase
  end

  assign shift_ones     = RV32B ? (operator_i == ALU_SLO) || (operator_i == ALU_SRO) : 1'b0;
  assign shift_arith    = (operator_i == ALU_SRA);
  assign shift_rot      = RV32B ? (operator_i == ALU_ROL) || (operator_i == ALU_ROR) : 1'b0;
  assign shift_funnel   = RV32B ? (operator_i == ALU_FSL) || (operator_i == ALU_FSR) : 1'b0;
  assign shift_multicycle = shift_funnel || shift_rot;

  assign shift_none     = RV32B ? (operator_i == ALU_REV)  || (operator_i == ALU_REV8) ||
                                      (operator_i == ALU_ORCB) :
                                  1'b0;

  assign shift_op_rev   = RV32B ? (operator_i == ALU_REV) : 1'b0;
  assign shift_op_rev8  = RV32B ? (operator_i == ALU_REV8) : 1'b0;
  assign shift_op_orc_b = RV32B ? (operator_i == ALU_ORCB) : 1'b0;

  logic [31:0] shift_result;
  logic [32:0] shift_result_ext;

  always_comb begin
    shift_result = operand_a_i;

    // select bit reversed or normal input
    if (shift_op_rev || shift_left) begin
      shift_result = operand_a_rev;
    end

    shift_result_ext = $signed({shift_ones || (shift_arith && shift_result[31]), shift_result})
        >>> shift_amt[4:0];

    // shift, if this is a shift operation
    if (!shift_none) begin
      shift_result = shift_result_ext[31:0];
    end

    // shift left: bytewise reverse. (orcombine with '0)
    // orc_b: bytewise reverse and orcombine.
    if (shift_op_orc_b || shift_left) begin
      shift_result = (shift_op_orc_b ? shift_result : 32'h 0) |
                     ((shift_result & 32'h 55555555) <<  1)   |
                     ((shift_result & 32'h AAAAAAAA) >>  1);

      shift_result = (shift_op_orc_b ? shift_result : 32'h 0) |
                     ((shift_result & 32'h 33333333) <<  2)   |
                     ((shift_result & 32'h CCCCCCCC) >>  2);

      shift_result = (shift_op_orc_b ? shift_result : 32'h 0) |
                     ((shift_result & 32'h 0F0F0F0F) <<  4)   |
                     ((shift_result & 32'h F0F0F0F0) >>  4);
    end

    // byte-swap
    if (shift_op_rev8 || shift_left) begin
      shift_result = ((shift_result & 32'h 00FF00FF) <<  8) |
                     ((shift_result & 32'h FF00FF00) >>  8);

      shift_result = ((shift_result & 32'h 0000FFFF) << 16) |
                     ((shift_result & 32'h FFFF0000) >> 16);
    end
  end

  ////////////////
  // Comparison //
  ////////////////

  logic is_equal;
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb begin
    unique case (operator_i)
      ALU_GE,
      ALU_LT,
      ALU_SLT,
      // RV32B only
      ALU_MIN,
      ALU_MAX: cmp_signed = 1'b1;

      default: cmp_signed = 1'b0;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);
  assign is_equal_result_o = is_equal;

  // Is greater equal
  always_comb begin
    if ((operand_a_i[31] ^ operand_b_i[31]) == 1'b0) begin
      is_greater_equal = (adder_result[31] == 1'b0);
    end else begin
      is_greater_equal = operand_a_i[31] ^ (cmp_signed);
    end
  end

  // GTE unsigned:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 1
  // (a[31] == 0 && b[31] == 1) => 0

  // GTE signed:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 0
  // (a[31] == 0 && b[31] == 1) => 1

  // generate comparison result
  logic cmp_result;

  always_comb begin
    unique case (operator_i)
      ALU_EQ:             cmp_result =  is_equal;
      ALU_NE:             cmp_result = ~is_equal;
      ALU_GE,   ALU_GEU,
      ALU_MAX,  ALU_MAXU: cmp_result = is_greater_equal; // RV32B only
      ALU_LT,   ALU_LTU,
      ALU_MIN,  ALU_MINU, //RV32B only
      ALU_SLT,  ALU_SLTU: cmp_result = ~is_greater_equal;

      default: cmp_result = is_equal;
    endcase
  end

  assign comparison_result_o = cmp_result;

  logic [31:0] minmax_result;
  logic [5:0]  bitcnt_result;
  logic [31:0] bwlogic_result;
  logic [31:0] pack_result;
  logic [31:0] multicycle_result;

  ///////////////////
  // Bitwise Logic //
  ///////////////////

  logic bwlogic_or;
  logic bwlogic_and;
  logic [31:0] bwlogic_operand_b;
  logic [31:0] bwlogic_or_op_a;
  logic [31:0] bwlogic_or_op_b;
  logic [31:0] bwlogic_or_result;
  logic [31:0] bwlogic_and_result;
  logic [31:0] bwlogic_xor_result;

  logic bwlogic_op_b_negate;

  always_comb begin
    unique case (operator_i)
      // Logic-with-negate OPs (RV32B Ops)
      ALU_XNOR,
      ALU_ORN,
      ALU_ANDN: bwlogic_op_b_negate = RV32B ? 1'b1 : 1'b0;
      ALU_CMIX: bwlogic_op_b_negate = RV32B ? !instr_first_cycle_i : 1'b0;
      default: bwlogic_op_b_negate = 1'b0;
    endcase
  end

  assign bwlogic_operand_b = bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b_i;
  assign bwlogic_or_op_a = ((operator_i == ALU_CMIX) || shift_multicycle) ?
                           imd_val_q_i : operand_a_i;
  assign bwlogic_or_op_b = (operator_i == ALU_CMIX) ? bwlogic_and_result :
                           shift_multicycle         ? shift_result       : bwlogic_operand_b;

  assign bwlogic_or_result = bwlogic_or_op_a | bwlogic_or_op_b;

  assign bwlogic_and_result = operand_a_i & bwlogic_operand_b;
  assign bwlogic_xor_result = operand_a_i ^ bwlogic_operand_b;

  assign bwlogic_or  = (operator_i == ALU_OR) || (operator_i == ALU_ORN);
  assign bwlogic_and = (operator_i == ALU_AND) || (operator_i == ALU_ANDN);

  always_comb begin
    unique case (1'b1)
      bwlogic_or:  bwlogic_result = bwlogic_or_result;
      bwlogic_and: bwlogic_result = bwlogic_and_result;
      default:     bwlogic_result = bwlogic_xor_result;
    endcase
  end

  if (RV32B) begin : g_alu_rvb

    //////////////////////////////////////
    // Multicycle Bitmanip Instructions //
    //////////////////////////////////////
    // Ternary instructions + Shift Rotations
    // For ternary instructions (zbt), operand_a_i is tied to rs1 in the first cycle and rs3 in the
    // second cycle. operand_b_i is always tied to rs2.

    always_comb begin
      unique case (operator_i)
        ALU_CMOV: begin
            imd_val_d_o = operand_a_i;
            multicycle_result = (operand_b_i == 32'h0) ? operand_a_i : imd_val_q_i;
          if (instr_first_cycle_i) begin
            imd_val_we_o = 1'b1;
          end else begin
            imd_val_we_o = 1'b0;
          end
        end

        ALU_CMIX: begin
          multicycle_result = bwlogic_or_result;
          imd_val_d_o = bwlogic_and_result;
          if (instr_first_cycle_i) begin
            imd_val_we_o = 1'b1;
          end else begin
            imd_val_we_o = 1'b0;
          end
        end

        ALU_FSR, ALU_FSL,
        ALU_ROL, ALU_ROR: begin
          if (shift_amt[4:0] == 5'h0) begin
            multicycle_result = shift_amt[5] ? operand_a_i : imd_val_q_i;
          end else begin
            multicycle_result = bwlogic_or_result;
          end
          imd_val_d_o = shift_result;
          if (instr_first_cycle_i) begin
            imd_val_we_o = 1'b1;
          end else begin
            imd_val_we_o = 1'b0;
          end
        end
        default: begin
          imd_val_d_o = operand_a_i;
          imd_val_we_o = 1'b0;
          multicycle_result = operand_a_i;
        end
      endcase
    end

    ///////////////
    // Min / Max //
    ///////////////

    assign minmax_result = (cmp_result ? operand_a_i : operand_b_i);

    /////////////////
    // Bitcounting //
    /////////////////

    logic        bitcnt_ctz;
    logic        bitcnt_pcnt;
    logic [31:0] bitcnt_bits;
    logic [32:0] bitcnt_bit_enable;

    assign bitcnt_ctz  = (operator_i == ALU_CTZ);
    assign bitcnt_pcnt = (operator_i == ALU_PCNT);

    assign bitcnt_bits = bitcnt_pcnt ? operand_a_i : (bitcnt_ctz ? ~operand_a_i : ~operand_a_rev);

    always_comb begin
      bitcnt_result = '0;
      bitcnt_bit_enable = {32'b0, 1'b1}; // bit 32 unused.
      for (int unsigned i=0; i<32; i++) begin : gen_bitcnt_adder
        // keep counting if all previous bits are 1
        bitcnt_bit_enable[i+1] = bitcnt_pcnt || (bitcnt_bit_enable[i] && bitcnt_bits[i]);
        if (bitcnt_bit_enable[i]) begin
          bitcnt_result[5:0] = bitcnt_result[5:0] + {5'h0, bitcnt_bits[i]};
        end
      end
    end

    //////////
    // Pack //
    //////////

    logic packu;
    logic packh;
    assign packu = (operator_i == ALU_PACKU);
    assign packh = (operator_i == ALU_PACKH);

    always_comb begin
      unique case (1'b1)
        packu:   pack_result = {operand_b_i[31:16], operand_a_i[31:16]};
        packh:   pack_result = {16'h0, operand_b_i[7:0], operand_a_i[7:0]};
        default: pack_result = {operand_b_i[15:0], operand_a_i[15:0]};
      endcase
    end
  end else begin : g_no_alu_rvb
    // RV32B result signals
    assign minmax_result     = '0;
    assign bitcnt_result     = '0;
    assign pack_result       = '0;
    assign multicycle_result = '0;
    // RV32B support signals
    assign imd_val_d_o  = '0;
    assign imd_val_we_o = '0;
  end

  ////////////////
  // Result mux //
  ////////////////

  always_comb begin
    result_o   = '0;

    unique case (operator_i)
      // Bitwise Logic Operations (negate: RV32B Ops)
      ALU_XOR, ALU_XNOR,
      ALU_OR,  ALU_ORN,
      ALU_AND, ALU_ANDN: result_o = bwlogic_result;

      // Adder Operations
      ALU_ADD, ALU_SUB: result_o = adder_result;

      // Shift Operations
      ALU_SLL, ALU_SRL,
      ALU_SRA,
      // RV32B Ops
      ALU_SLO, ALU_SRO,
      ALU_REV, ALU_REV8,
      ALU_ORCB: result_o = shift_result;

      // Comparison Operations
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU: result_o = {31'h0,cmp_result};

      // MinMax Operations (RV32B Ops)
      ALU_MIN,  ALU_MAX,
      ALU_MINU, ALU_MAXU: result_o = minmax_result;

      // Bitcount Operations (RV32B Ops)
      ALU_CLZ, ALU_CTZ,
      ALU_PCNT: result_o = {26'h0, bitcnt_result};

      // Pack Operations (RV32B Ops)
      ALU_PACK, ALU_PACKH,
      ALU_PACKU: result_o = pack_result;

      // Ternary Bitmanip Operations (RV32B Ops)
      ALU_CMIX, ALU_CMOV,
      ALU_FSL,  ALU_FSR,
      ALU_ROL,  ALU_ROR: result_o = multicycle_result;

      default: ;
    endcase
  end

endmodule
