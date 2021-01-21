// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN alu block for the bignum instruction subset
 *
 * This ALU supports all of the 'plain' arithmetic and logic bignum instructions, BN.MULQACC is
 * implemented in a seperate block.
 *
 * One barrel shifter and two adders (X and Y) are implemented along with the logic operators
 * (AND,OR,XOR,NOT).
 *
 * The adders have 256-bit operands with a carry_in and optional invert on the second operand. This
 * can be used to implement subtraction (a - b == a + ~b + 1). BN.SUBB/BN.ADDC are implemented by
 * feeding in the carry flag as carry in rather than a fixed 0 or 1.
 *
 * The shifter takes a 512-bit input (to implement BN.RSHI, concatenate and right shift) and shifts
 * right by up to 256-bits. The lower (256-bit) half of the input and output can be reversed to
 * allow left shift implementation.  There is no concatenate and left shift instruction so reversing
 * isn't required over the full width.
 *
 * The dataflow between the adders and shifter is in the diagram below. This arrangement allows the
 * implementation of the pseudo-mod (BN.ADDM/BN.SUBM) instructions in a single cycle whilst
 * minimising the critical path. The pseudo-mod instructions do not have a shifted input so X can
 * compute the initial add/sub and Y computes the pseudo-mod result. For all other add/sub
 * operations Y computes the operation with one of the inputs supplied by the shifter and the other
 * from operand_a.
 *
 * Both adder X and the shifter get supplied with operand_a and operand_b from the operation_i
 * input. In addition the shifter gets a shift amount (shift_amt) and can use 0 instead of
 * operand_a. The shifter concatenates operand_a (or 0) and operand_b together before shifting with
 * operand_a in the upper (256-bit) half {operand_a/0, operand_b}. This allows the shifter to pass
 * through operand_b simply by not performing a shift.
 *
 *                     A 0
 *                     | |
 *                   \-----/
 *                    \---/
 *      A       B       |   B   shift_amt
 *      |       |       |   |   |
 *    +-----------+   +-----------+
 *    |  Adder X  |   |  Shifter  |
 *    +-----------+   +-----------+
 *          |               |
 *          |----+     +----|
 *          |    |     |    |
 *      X result |     | Shifter result
 *               |     |
 *               |     |     +-----------+
 *             A |     | +---|  MOD WSR  |
 *             | |     | |   +-----------+
 *           \-----/ \-----/
 *            \---/   \---/
 *              |       |
 *              |       |
 *            +-----------+
 *            |  Adder Y  |
 *            +-----------+
 *                  |
 *              Y result
 */


module otbn_alu_bignum
  import otbn_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  input  alu_bignum_operation_t operation_i,
  output logic [WLEN-1:0]       operation_result_o,

  input  ispr_e                       ispr_addr_i,
  input  logic [31:0]                 ispr_base_wdata_i,
  input  logic [BaseWordsPerWLEN-1:0] ispr_base_wr_en_i,
  input  logic [WLEN-1:0]             ispr_bignum_wdata_i,
  input  logic                        ispr_bignum_wr_en_i,
  output logic [WLEN-1:0]             ispr_rdata_o,

  input  logic [WLEN-1:0]             ispr_acc_i,
  output logic [WLEN-1:0]             ispr_acc_wr_data_o,
  output logic                        ispr_acc_wr_en_o,

  input  flags_t                      mac_operation_flags_i,
  input  flags_t                      mac_operation_flags_en_i,

  input  logic [WLEN-1:0]             rnd_i
);
  ///////////
  // ISPRs //
  ///////////

  flags_t                              flags_q [NFlagGroups];
  flags_t                              flags_d [NFlagGroups];
  logic   [NFlagGroups*FlagsWidth-1:0] flags_flattened;
  logic   [NFlagGroups-1:0]            flags_en;
  logic   [NFlagGroups-1:0]            is_operation_flag_group;
  flags_t                              selected_flags;
  flags_t                              adder_update_flags;
  logic                                adder_update_flags_en, adder_update_flags_en_raw;
  flags_t                              logic_update_flags;
  logic                                logic_update_flags_en, logic_update_flags_en_raw;
  flags_t                              mac_update_flags;
  logic                                mac_update_flags_en;
  logic                                ispr_update_flags_en;

  assign adder_update_flags_en = operation_i.alu_flag_en & adder_update_flags_en_raw;
  assign logic_update_flags_en = operation_i.alu_flag_en & logic_update_flags_en_raw;
  assign mac_update_flags_en   = operation_i.mac_flag_en;

  assign ispr_update_flags_en = (ispr_base_wr_en_i[0] & (ispr_addr_i == IsprFlags));


  `ASSERT(UpdateFlagsOnehot,
          $onehot0({adder_update_flags_en, logic_update_flags_en, mac_update_flags_en,
                    ispr_update_flags_en}))

  assign selected_flags = flags_q[operation_i.flag_group];

  assign mac_update_flags = (selected_flags        & ~mac_operation_flags_en_i) |
                            (mac_operation_flags_i &  mac_operation_flags_en_i);

  for (genvar i_fg = 0; i_fg < NFlagGroups; i_fg++) begin : g_flag_groups
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        flags_q[i_fg] <= '{Z : 1'b0, L : 1'b0, M : 1'b0, C : 1'b0};
      end else if (flags_en[i_fg]) begin
        flags_q[i_fg] <= flags_d[i_fg];
      end
    end

    assign is_operation_flag_group[i_fg] = operation_i.flag_group == i_fg;

    assign flags_flattened[i_fg * FlagsWidth +: FlagsWidth] = flags_q[i_fg];

    // Flag updates can come from the Y adder result, the logical operation result or from an ISPR
    // write.
    always_comb begin
      flags_d[i_fg] = adder_update_flags;

      unique case (1'b1)
        adder_update_flags_en: flags_d[i_fg] = adder_update_flags;
        logic_update_flags_en: flags_d[i_fg] = logic_update_flags;
        mac_update_flags_en:   flags_d[i_fg] = mac_update_flags;
        ispr_update_flags_en:  flags_d[i_fg] = ispr_base_wdata_i[i_fg * FlagsWidth +: FlagsWidth];
        default: ;
      endcase
    end

    assign flags_en[i_fg] = ispr_update_flags_en |
      (adder_update_flags_en & is_operation_flag_group[i_fg]) |
      (logic_update_flags_en & is_operation_flag_group[i_fg]) |
      (mac_update_flags_en   & is_operation_flag_group[i_fg]);
  end


  logic [WLEN-1:0]             mod_q;
  logic [WLEN-1:0]             mod_d;
  logic [BaseWordsPerWLEN-1:0] mod_wr_en;

  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_mod_words
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mod_q[i_word*32+:32] <= '0;
      end else if (mod_wr_en[i_word]) begin
        mod_q[i_word*32+:32] <= mod_d[i_word*32+:32];
      end
    end

    assign mod_d[i_word*32+:32] = ispr_base_wr_en_i[i_word] ? ispr_base_wdata_i :
                                                              ispr_bignum_wdata_i[i_word*32+:32];

    assign mod_wr_en[i_word] = (ispr_addr_i == IsprMod) & (ispr_base_wr_en_i[i_word] |
                                                           ispr_bignum_wr_en_i);
  end

  assign ispr_acc_wr_en_o   = (ispr_addr_i == IsprAcc) & ispr_bignum_wr_en_i;
  assign ispr_acc_wr_data_o = ispr_bignum_wdata_i;

  always_comb begin
    ispr_rdata_o = mod_q;

    unique case (ispr_addr_i)
      IsprMod:   ispr_rdata_o = mod_q;
      IsprRnd:   ispr_rdata_o = rnd_i;
      IsprAcc:   ispr_rdata_o = ispr_acc_i;
      IsprFlags: ispr_rdata_o = {{(WLEN - (NFlagGroups * FlagsWidth)){1'b0}}, flags_flattened};
      default: ;
    endcase
  end

  /////////////
  // Shifter //
  /////////////

  logic              shift_right;
  logic [WLEN-1:0]   shifter_in_upper, shifter_in_lower, shifter_in_lower_reverse;
  logic [WLEN*2-1:0] shifter_in;
  logic [WLEN*2-1:0] shifter_out;
  logic [WLEN-1:0]   shifter_out_lower_reverse, shifter_res, unused_shifter_out_upper;

  assign shifter_in_upper = operation_i.op == AluOpBignumRshi ? operation_i.operand_a : '0;
  assign shifter_in_lower = operation_i.operand_b;

  for (genvar i = 0; i < WLEN; i++) begin : g_shifter_in_lower_reverse
    assign shifter_in_lower_reverse[i] = shifter_in_lower[WLEN - i - 1];
  end

  assign shifter_in = {shifter_in_upper, shift_right ? shifter_in_lower :
                                                       shifter_in_lower_reverse};

  assign shifter_out = shifter_in >> operation_i.shift_amt;

  for (genvar i = 0; i < WLEN; i++) begin : g_shifter_out_lower_reverse
    assign shifter_out_lower_reverse[i] = shifter_out[WLEN - i - 1];
  end

  assign shifter_res = shift_right ? shifter_out[WLEN-1:0] : shifter_out_lower_reverse;

  // Only the lower WLEN bits of the shift result are returned.
  assign unused_shifter_out_upper = shifter_out[WLEN*2-1:WLEN];

  //////////////////
  // Adders X & Y //
  //////////////////

  logic [WLEN:0]   adder_x_op_a, adder_x_op_b;
  logic            adder_x_carry_in;
  logic            adder_x_op_b_invert;
  logic [WLEN+1:0] adder_x_res;

  logic [WLEN:0]   adder_y_op_a, adder_y_op_b;
  logic            adder_y_carry_in;
  logic            adder_y_op_b_invert;
  logic [WLEN+1:0] adder_y_res;

  logic            shift_mod_sel;
  logic [WLEN-1:0] shift_mod_mux_out;
  logic            x_res_operand_a_sel;
  logic [WLEN-1:0] x_res_operand_a_mux_out;

  assign adder_x_op_a = {operation_i.operand_a, 1'b1};
  assign adder_x_op_b = {adder_x_op_b_invert ? ~operation_i.operand_b : operation_i.operand_b,
                         adder_x_carry_in};

  assign adder_x_res = adder_x_op_a + adder_x_op_b;

  assign x_res_operand_a_mux_out = x_res_operand_a_sel ? adder_x_res[WLEN:1] :
                                                         operation_i.operand_a;
  assign shift_mod_mux_out = shift_mod_sel ? shifter_res : mod_q;

  assign adder_y_op_a = {x_res_operand_a_mux_out, 1'b1};
  assign adder_y_op_b = {adder_y_op_b_invert ? ~shift_mod_mux_out : shift_mod_mux_out,
                         adder_y_carry_in};

  assign adder_y_res = adder_y_op_a + adder_y_op_b;

  assign adder_update_flags.C = (operation_i.op == AluOpBignumAdd ||
                                 operation_i.op == AluOpBignumAddc) ?  adder_y_res[WLEN+1] :
                                                                      ~adder_y_res[WLEN+1];
  assign adder_update_flags.M = adder_y_res[WLEN];
  assign adder_update_flags.L = adder_y_res[1];
  assign adder_update_flags.Z = ~|adder_y_res[WLEN:1];

  // The LSb of the adder results are unused.
  logic unused_adder_x_res_lsb, unused_adder_y_res_lsb;
  assign unused_adder_x_res_lsb = adder_x_res[0];
  assign unused_adder_y_res_lsb = adder_y_res[0];

  //////////////////////////////
  // Shifter & Adders control //
  //////////////////////////////

  always_comb begin
    shift_right               = 1'b0;
    adder_x_carry_in          = 1'b0;
    adder_x_op_b_invert       = 1'b0;
    x_res_operand_a_sel       = 1'b0;
    shift_mod_sel             = 1'b0;
    adder_y_carry_in          = 1'b0;
    adder_y_op_b_invert       = 1'b0;
    adder_update_flags_en_raw = 1'b0;
    logic_update_flags_en_raw = 1'b0;

    unique case (operation_i.op)
      AluOpBignumAdd: begin
        // Shifter computes B [>>|<<] shift_amt
        // Y computes A + shifter_res
        // X ignored
        shift_right               = operation_i.shift_right;
        x_res_operand_a_sel       = 1'b0;
        shift_mod_sel             = 1'b1;
        adder_y_carry_in          = 1'b0;
        adder_y_op_b_invert       = 1'b0;
        adder_update_flags_en_raw = 1'b1;
      end
      AluOpBignumAddc: begin
        // Shifter computes B [>>|<<] shift_amt
        // Y computes A + shifter_res + flags.C
        // X ignored
        shift_right               = operation_i.shift_right;
        x_res_operand_a_sel       = 1'b0;
        shift_mod_sel             = 1'b1;
        adder_y_carry_in          = selected_flags.C;
        adder_y_op_b_invert       = 1'b0;
        adder_update_flags_en_raw = 1'b1;
      end
      AluOpBignumAddm: begin
        // X computes A + B
        // Y computes adder_x_res - mod = adder_x_res + ~mod + 1
        // Shifter ignored
        // Output mux chooses result based on top bit of X result (whether mod subtraction in
        // Y should be applied or not)
        adder_x_carry_in    = 1'b0;
        adder_x_op_b_invert = 1'b0;
        x_res_operand_a_sel = 1'b1;
        shift_mod_sel       = 1'b0;
        adder_y_carry_in    = 1'b1;
        adder_y_op_b_invert = 1'b1;
      end
      AluOpBignumSub: begin
        // Shifter computes B [>>|<<] shift_amt
        // Y computes A - shifter_res = A + ~shifter_res + 1
        // X ignored
        shift_right               = operation_i.shift_right;
        x_res_operand_a_sel       = 1'b0;
        shift_mod_sel             = 1'b1;
        adder_y_carry_in          = 1'b1;
        adder_y_op_b_invert       = 1'b1;
        adder_update_flags_en_raw = 1'b1;
      end
      AluOpBignumSubb: begin
        // Shifter computes B [>>|<<] shift_amt
        // Y computes A - shifter_res + ~flags.C = A + ~shifter_res + flags.C
        // X ignored
        shift_right               = operation_i.shift_right;
        x_res_operand_a_sel       = 1'b0;
        shift_mod_sel             = 1'b1;
        adder_y_carry_in          = ~selected_flags.C;
        adder_y_op_b_invert       = 1'b1;
        adder_update_flags_en_raw = 1'b1;
      end
      AluOpBignumSubm: begin
        // X computes A - B = A + ~B + 1
        // Y computes adder_x_res + mod
        // Shifter ignored
        // Output mux chooses result based on top bit of X result (whether subtraction in Y should
        // be applied or not)
        adder_x_carry_in    = 1'b1;
        adder_x_op_b_invert = 1'b1;
        x_res_operand_a_sel = 1'b1;
        shift_mod_sel       = 1'b0;
        adder_y_carry_in    = 1'b0;
        adder_y_op_b_invert = 1'b0;
      end
      AluOpBignumRshi: begin
        // Shifter computes {A, B} >> shift_amt
        // X, Y ignored
        shift_right = 1'b1;
      end
      AluOpBignumXor,
      AluOpBignumOr,
      AluOpBignumAnd,
      AluOpBignumNot: begin
        // Shift computes one operand for the logical operation
        // X & Y ignored
        shift_right               = operation_i.shift_right;
        logic_update_flags_en_raw = 1'b1;
      end
      default: ;
    endcase
  end

  ////////////////////////
  // Logical operations //
  ////////////////////////

  logic [WLEN-1:0] logical_res;

  always_comb begin
    logical_res = ~operation_i.operand_a;

    unique case (operation_i.op)
      AluOpBignumXor: logical_res = operation_i.operand_a ^ shifter_res;
      AluOpBignumOr:  logical_res = operation_i.operand_a | shifter_res;
      AluOpBignumAnd: logical_res = operation_i.operand_a & shifter_res;
      AluOpBignumNot: logical_res = ~shifter_res;
      default:;
    endcase
  end

  // Logical operations only update M, L and Z; C must remain at its old value.
  assign logic_update_flags.C = selected_flags.C;
  assign logic_update_flags.M = logical_res[WLEN-1];
  assign logic_update_flags.L = logical_res[0];
  assign logic_update_flags.Z = ~|logical_res;

  ////////////////////////
  // Conditional Select //
  ////////////////////////

  logic [WLEN-1:0] sel_res;
  logic            sel_flag;

  always_comb begin
    unique case (operation_i.sel_flag)
      FlagC:   sel_flag = selected_flags.C;
      FlagL:   sel_flag = selected_flags.L;
      FlagM:   sel_flag = selected_flags.M;
      FlagZ:   sel_flag = selected_flags.Z;
      default: sel_flag = selected_flags.C;
    endcase
  end

  `ASSERT(SelFlagValid,
      operation_i.op == AluOpBignumSel |-> operation_i.sel_flag inside {FlagC, FlagL, FlagM, FlagZ})

  assign sel_res = (sel_flag || operation_i.op == AluOpBignumMov) ? operation_i.operand_a :
                                                                    operation_i.operand_b;

  ////////////////////////
  // Output multiplexer //
  ////////////////////////

  always_comb begin
    operation_result_o = adder_y_res[WLEN:1];

    unique case(operation_i.op)
      AluOpBignumAdd,
      AluOpBignumAddc,
      AluOpBignumSub,
      AluOpBignumSubb: begin
        operation_result_o = adder_y_res[WLEN:1];
      end

      // For pseudo-mod operations the result depends upon initial a + b / a - b result that is
      // computed in X. Operation to add/subtract mod (X + mod / X - mod) is computed in Y.
      // Subtraction is computed using in the X & Y adders as a - b == a + ~b + 1. Note that for
      // a - b the top bit of the result will be set if a - b >= 0 and otherwise clear.

      // BN.ADDM - X = a + b, Y = X - mod, subtract mod if a + b >= mod
      // * If X generates carry a + b > mod (as mod is 256-bit) - Select Y result
      // * If Y generates carry X - mod == (a + b) - mod >= 0 hence a + b >= mod, note this is only
      //   valid if X does not generate carry - Select Y result
      // * If neither happen a + b < mod - Select X result
      AluOpBignumAddm: begin
        if (adder_x_res[WLEN+1] || adder_y_res[WLEN+1]) begin
          operation_result_o = adder_y_res[WLEN:1];
        end else begin
          operation_result_o = adder_x_res[WLEN:1];
        end
      end

      // BN.SUBM - X = a - b, Y = X + mod, add mod if a - b < 0
      // * If X generates carry a - b >= 0 - Select X result
      // * Otherwise select Y result
      AluOpBignumSubm: begin
        if (adder_x_res[WLEN+1]) begin
          operation_result_o = adder_x_res[WLEN:1];
        end else begin
          operation_result_o = adder_y_res[WLEN:1];
        end
      end

      AluOpBignumRshi: begin
        operation_result_o = shifter_res[WLEN-1:0];
      end

      AluOpBignumXor,
      AluOpBignumOr,
      AluOpBignumAnd,
      AluOpBignumNot: begin
        operation_result_o = logical_res;
      end

      AluOpBignumSel,
      AluOpBignumMov: begin
        operation_result_o = sel_res;
      end
      default: ;
    endcase
  end
endmodule
