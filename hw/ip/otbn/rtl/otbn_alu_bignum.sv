// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
/**
 * OTBN alu block for the bignum instruction subset
 *
 * This ALU supports all of the 'plain' arithmetic and logic bignum instructions and some
 * vectorized arithmetic instructions. BN.MULQACC and its vectorized counterparts are
 * implemented in a separate block.
 *
 * One barrel shifter and two adders (X and Y) are implemented along with the logic operators
 * (AND,OR,XOR,NOT), a vector transposer and 24-bit to 32-bit packing and unpacking logic.
 *
 * The adders have 256-bit operands with a carry_in and optional invert on the second operand. This
 * can be used to implement subtraction (a - b == a + ~b + 1). BN.SUBB/BN.ADDC are implemented by
 * feeding in the carry flag as carry in rather than a fixed 0 or 1. These 256-bit operands can
 * also be interpreted as vectors with 32-bit elements.
 *
 * The shifter takes a 512-bit input (to implement BN.RSHI, concatenate and right shift) and shifts
 * right by up to 256-bits. The lower (256-bit) half of the input and output can be reversed to
 * allow left shift implementation. There is no concatenate and left shift instruction so reversing
 * isn't required over the full width.
 *
 * The dataflow between the adders and shifter is in the diagram below. This arrangement allows the
 * implementation of the pseudo-mod (BN.ADDM(V)/BN.SUBM(V)) instructions in a single cycle whilst
 * minimising the critical path. The pseudo-mod instructions do not have a shifted input so X can
 * compute the initial add/sub and Y computes the pseudo-mod result. The result is selected based
 * on the carries of adder X and Y. This selection logic is implemented in the modulo result
 * selector. For all other add/sub operations, Y computes the operation with one of the inputs
 * supplied by the shifter and the other from operand_a. The result is then pushed through the
 * modulo result selector. This allows to save one input to the final result selection mux.
 *
 * The shifter gets supplied with either operand_a and operand_b or a dense representation thereof
 * to implement the packing functionality. In addition, the shifter gets a shift amount (shift_amt)
 * and can use 0 instead of operand_a / its dense representation. The shifter concatenates both
 * inputs together before shifting with operand_a in the upper (256-bit) half {A/0, B}. This
 * allows the shifter to pass through operand_b simply by not performing a shift.
 *
 * The shifter result has no direct connection to the final result MUX but the result is pushed
 * through the logic block with operand_a set to 0 and the logic operation set to OR. This saves
 * one input to the result selection mux.
 *
 * The vector packing and unpacking is implemented using the shifter's concatenation feature and
 * some wiring.
 *
 * Blanking is employed on the ALU data paths. This holds unused data paths to 0 to reduce side
 * channel leakage. The lower-case 'b' on the diagram below indicates points in the data path that
 * get blanked. Note that Adder X is never used in isolation, it is always combined with Adder Y so
 * there is no need for blanking between Adder X and Adder Y.
 *
 * Due to this blanking only one of the possible results can be active at the same time. This
 * allows to implement the final result selection with one 256-bit OR. This is more area as well
 * as timing efficient compared to a regular 256-bit mux.
 *
 *                          A     B
 *                          |     |
 *                          b     b
 *                          |     |
 *                     +----+     +----+
 *                     |    |     |    |
 *                     |  +---------+  |
 *                     |  | Packing |  |
 *                     |  +---------+  |
 *     A       B       |   |       |   |
 *     |       |     \-------/   \-------/
 *     b       b      \-----/     \-----/
 *     |       |         |           |
 *   +-----------+    +-----------------+
 *   |  Adder X  |    |     Shifter     |
 *   +-----------+    +-----------------+
 *         |                   |
 *   +-----+-----+     +-------+-------------+
 *   |     |     |     |       |             |
 *   |  X result |     |  shifter result     |
 *   |           |     |                     |
 *   |         A |     |     +-----------+   |
 *   |         | |     | +---|  MOD WSR  |   |
 *   |         b |     b |   +-----------+   |
 *   |         | |     | |                   |
 *   |       \-----/ \-----/          +------+------+   A         A       B
 *   |        \---/   \---/           |             |   |         |       |
 *   |          |       |             b             b   b         b       b
 *   |          |       |             |             |   |         |       |
 *   |        +-----------+     +-----------+     +-------+     +-----------+
 *   |        |  Adder Y  |     | Unpacking |     | Logic |     | Transpose |
 *   |        +-----------+     +-----------+     +-------+     +-----------+
 *   |              |                 |               |               |
 *   +------+    Y result             |               |               |
 *          |       |                 |               |               |
 *        +-----------+               |               |               |
 *        | Modulo    |               |               |               |
 *        | Result    |               |               |               |
 *        | Selection |               |               |               |
 *        +-----------+               |               |               |
 *              |                     |               |               |
 *      arithmetic result      unpacked result   logic result  transpose result
 *              |                     |               |               |
 *            +---------------------------------------------------------+
 *            |                            OR                           |
 *            +---------------------------------------------------------+
 *                                         |
 *                                 operation_result_o
 */
module otbn_alu_bignum
  import otbn_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  input  alu_bignum_operation_t operation_i,
  input  logic                  operation_valid_i,
  input  logic                  operation_commit_i, // used for SVAs only
  output logic [WLEN-1:0]       operation_result_o,
  output logic                  selection_flag_o,

  input  alu_bignum_predec_t  alu_bignum_predec_i,
  input  ispr_bignum_predec_t ispr_bignum_predec_i,

  input  ispr_e                       ispr_addr_i,
  input  logic [31:0]                 ispr_base_wdata_i,
  input  logic [BaseWordsPerWLEN-1:0] ispr_base_wr_en_i,
  input  logic [ExtWLEN-1:0]          ispr_bignum_wdata_intg_i,
  input  logic                        ispr_bignum_wr_en_i,
  input  logic [NFlagGroups-1:0]      ispr_flags_wr_i,
  input  logic                        ispr_wr_commit_i,
  input  logic                        ispr_init_i,
  output logic [ExtWLEN-1:0]          ispr_rdata_intg_o,
  input  logic                        ispr_rd_en_i,

  input  logic [ExtWLEN-1:0]          ispr_acc_intg_i,
  output logic [ExtWLEN-1:0]          ispr_acc_wr_data_intg_o,
  output logic                        ispr_acc_wr_en_o,

  output logic                        reg_intg_violation_err_o,

  input  logic                        sec_wipe_mod_urnd_i,
  input  logic                        sec_wipe_running_i,
  output logic                        sec_wipe_err_o,

  input  flags_t                      mac_operation_flags_i,
  input  flags_t                      mac_operation_flags_en_i,

  input  logic [WLEN-1:0]             rnd_data_i,
  input  logic [WLEN-1:0]             urnd_data_i,

  input  logic [1:0][SideloadKeyWidth-1:0] sideload_key_shares_i,

  output logic alu_predec_error_o,
  output logic ispr_predec_error_o
);

  logic [WLEN-1:0]     adder_y_res;
  logic [NVecProc-1:0] adder_y_carries_out;
  logic [WLEN-1:0]     logical_res;

  ///////////
  // ISPRs //
  ///////////

  flags_t                              flags_d [NFlagGroups];
  flags_t                              flags_q [NFlagGroups];
  logic   [NFlagGroups*FlagsWidth-1:0] flags_flattened;
  flags_t                              selected_flags;
  flags_t                              adder_update_flags;
  logic                                adder_update_flags_en_raw;
  flags_t                              logic_update_flags [NFlagGroups];
  logic                                logic_update_flags_en_raw;
  flags_t                              mac_update_flags [NFlagGroups];
  logic [NFlagGroups-1:0]              mac_update_z_flag_en_blanked;
  flags_t                              ispr_update_flags [NFlagGroups];

  logic [NIspr-1:0] expected_ispr_rd_en_onehot;
  logic [NIspr-1:0] expected_ispr_wr_en_onehot;
  logic             ispr_wr_en;

  logic [NFlagGroups-1:0] expected_flag_group_sel;
  flags_t                 expected_flag_sel;
  logic [NFlagGroups-1:0] expected_flags_keep;
  logic [NFlagGroups-1:0] expected_flags_adder_update;
  logic [NFlagGroups-1:0] expected_flags_logic_update;
  logic [NFlagGroups-1:0] expected_flags_mac_update;
  logic [NFlagGroups-1:0] expected_flags_ispr_wr;

  /////////////////////
  // Flags Selection //
  /////////////////////

  always_comb begin
    expected_flag_group_sel = '0;
    expected_flag_group_sel[operation_i.flag_group] = 1'b1;
  end
  assign expected_flag_sel.C = operation_i.sel_flag == FlagC;
  assign expected_flag_sel.M = operation_i.sel_flag == FlagM;
  assign expected_flag_sel.L = operation_i.sel_flag == FlagL;
  assign expected_flag_sel.Z = operation_i.sel_flag == FlagZ;

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width(FlagsWidth),
    .Inputs(NFlagGroups)
  ) u_flags_q_mux (
    .clk_i,
    .rst_ni,
    .in_i (flags_q),
    .sel_i(alu_bignum_predec_i.flag_group_sel),
    .out_o(selected_flags)
  );

  `ASSERT(BlankingSelectedFlags_A, expected_flag_group_sel == '0 |-> selected_flags == '0, clk_i,
    !rst_ni || alu_predec_error_o  || !operation_commit_i)

  logic                  flag_mux_in [FlagsWidth];
  logic [FlagsWidth-1:0] flag_mux_sel;
  assign flag_mux_in = '{selected_flags.C,
                         selected_flags.M,
                         selected_flags.L,
                         selected_flags.Z};
  assign flag_mux_sel = {alu_bignum_predec_i.flag_sel.Z,
                         alu_bignum_predec_i.flag_sel.L,
                         alu_bignum_predec_i.flag_sel.M,
                         alu_bignum_predec_i.flag_sel.C};

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width(1),
    .Inputs(FlagsWidth)
  ) u_flag_mux (
    .clk_i,
    .rst_ni,
    .in_i (flag_mux_in),
    .sel_i(flag_mux_sel),
    .out_o(selection_flag_o)
  );

  `ASSERT(BlankingSelectionFlag_A, expected_flag_sel == '0 |-> selection_flag_o == '0, clk_i,
    !rst_ni || alu_predec_error_o  || !operation_commit_i)

  //////////////////
  // Flags Update //
  //////////////////

  // Flags are only updated for regular 256b operations.
  // Vectorized operations do not update the flags.
  `ASSERT(VecAndModAndRshiOpsNoFlagUpdate_A,
          operation_i.op inside {AluOpBignumAddv, AluOpBignumSubv,
                                 AluOpBignumAddm, AluOpBignumAddvm,
                                 AluOpBignumSubm, AluOpBignumSubvm,
                                 AluOpBignumTrn1, AluOpBignumTrn2,
                                 AluOpBignumShv,
                                 AluOpBignumPack, AluOpBignumUnpk,
                                 AluOpBignumRshi}
          |-> !adder_update_flags_en_raw && !logic_update_flags_en_raw,
          clk_i, !rst_ni || !operation_commit_i)

  // Note that the flag zeroing triggered by ispr_init_i and secure wipe is achieved by not
  // selecting any inputs in the one-hot muxes below. The instruction fetch/predecoder stage
  // is driving the selector inputs accordingly.

  always_comb begin
    expected_flags_adder_update = '0;
    expected_flags_logic_update = '0;
    expected_flags_mac_update   = '0;

    expected_flags_adder_update[operation_i.flag_group] = operation_i.alu_flag_en &
                                                          adder_update_flags_en_raw;
    expected_flags_logic_update[operation_i.flag_group] = operation_i.alu_flag_en &
                                                          logic_update_flags_en_raw;
    expected_flags_mac_update[operation_i.flag_group]   = operation_i.mac_flag_en;
  end
  assign expected_flags_ispr_wr = ispr_flags_wr_i;

  assign expected_flags_keep = ~(expected_flags_adder_update |
                                 expected_flags_logic_update |
                                 expected_flags_mac_update |
                                 expected_flags_ispr_wr);

  // Adder operations update all flags.
  assign adder_update_flags.C = (operation_i.op == AluOpBignumAdd ||
                                 operation_i.op == AluOpBignumAddc) ?
                                 adder_y_carries_out[NVecProc-1] : ~adder_y_carries_out[NVecProc-1];

  assign adder_update_flags.M = adder_y_res[WLEN-1];
  assign adder_update_flags.L = adder_y_res[0];
  assign adder_update_flags.Z = ~|adder_y_res;

  for (genvar i_fg = 0; i_fg < NFlagGroups; i_fg++) begin : g_update_flag_groups

    // Logical operations only update M, L and Z; C must remain at its old value.
    assign logic_update_flags[i_fg].C = flags_q[i_fg].C;
    assign logic_update_flags[i_fg].M = logical_res[WLEN-1];
    assign logic_update_flags[i_fg].L = logical_res[0];
    assign logic_update_flags[i_fg].Z = ~|logical_res;

    ///////////////
    // MAC Flags //
    ///////////////

    // MAC operations don't update C.
    assign mac_update_flags[i_fg].C = flags_q[i_fg].C;

    // Tie off unused signals.
    logic unused_mac_operation_flags;
    assign unused_mac_operation_flags = mac_operation_flags_i.C ^ mac_operation_flags_en_i.C;

    // MAC operations update M and L depending on the operation. The individual enable signals for
    // M and L are generated from flopped instruction bits with minimal logic. They are not data
    // dependent.
    assign mac_update_flags[i_fg].M = mac_operation_flags_en_i.M ?
                                      mac_operation_flags_i.M : flags_q[i_fg].M;
    assign mac_update_flags[i_fg].L = mac_operation_flags_en_i.L ?
                                      mac_operation_flags_i.L : flags_q[i_fg].L;

    // MAC operations update Z depending on the operation and data. For BN.MULQACC.SO, already the
    // enable signal is data dependent (it depends on the lower half of the accumulator result). As
    // a result the enable signal might change back and forth during instruction execution which may
    // lead to SCA leakage. There is nothing that can really be done to avoid this other than
    // pipelining the flag computation which has a performance impact.
    //
    // By blanking the enable signal for the other flag group, we can at least avoid leakage related
    // to the other flag group, i.e., we give the programmer a way to control where the leakage
    // happens.
    // SEC_CM: DATA_REG_SW.SCA
    prim_blanker #(.Width(1)) u_mac_z_flag_en_blanker (
      .in_i (mac_operation_flags_en_i.Z),
      .en_i (alu_bignum_predec_i.flags_mac_update[i_fg]),
      .out_o(mac_update_z_flag_en_blanked[i_fg])
    );
    assign mac_update_flags[i_fg].Z = mac_update_z_flag_en_blanked[i_fg] ?
                                      mac_operation_flags_i.Z : flags_q[i_fg].Z;

    // For ISPR writes, we get the full write data from the base ALU and will select the relevant
    // parts using the blankers and one-hot muxes below.
    assign ispr_update_flags[i_fg] = ispr_base_wdata_i[i_fg*FlagsWidth+:FlagsWidth];
  end

  localparam int NFlagsSrcs = 5;
  for (genvar i_fg = 0; i_fg < NFlagGroups; i_fg++) begin : g_flag_groups

    flags_t                flags_d_mux_in [NFlagsSrcs];
    logic [NFlagsSrcs-1:0] flags_d_mux_sel;
    assign flags_d_mux_in = '{ispr_update_flags[i_fg],
                              mac_update_flags[i_fg],
                              logic_update_flags[i_fg],
                              adder_update_flags,
                              flags_q[i_fg]};
    assign flags_d_mux_sel = {alu_bignum_predec_i.flags_keep[i_fg],
                              alu_bignum_predec_i.flags_adder_update[i_fg],
                              alu_bignum_predec_i.flags_logic_update[i_fg],
                              alu_bignum_predec_i.flags_mac_update[i_fg],
                              alu_bignum_predec_i.flags_ispr_wr[i_fg]};

    // SEC_CM: DATA_REG_SW.SCA
    prim_onehot_mux #(
      .Width(FlagsWidth),
      .Inputs(NFlagsSrcs)
    ) u_flags_d_mux (
      .clk_i,
      .rst_ni,
      .in_i (flags_d_mux_in),
      .sel_i(flags_d_mux_sel),
      .out_o(flags_d[i_fg])
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        flags_q[i_fg] <= '{Z : 1'b0, L : 1'b0, M : 1'b0, C : 1'b0};
      end else begin
        flags_q[i_fg] <= flags_d[i_fg];
      end
    end

    assign flags_flattened[i_fg*FlagsWidth+:FlagsWidth] = flags_q[i_fg];
  end

  /////////
  // MOD //
  /////////

  logic [ExtWLEN-1:0]          mod_intg_q;
  logic [ExtWLEN-1:0]          mod_intg_d;
  logic [BaseWordsPerWLEN-1:0] mod_ispr_wr_en;
  logic [BaseWordsPerWLEN-1:0] mod_wr_en;

  logic [ExtWLEN-1:0] ispr_mod_bignum_wdata_intg_blanked;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(ExtWLEN)) u_ispr_mod_bignum_wdata_blanker (
    .in_i (ispr_bignum_wdata_intg_i),
    .en_i (ispr_bignum_predec_i.ispr_wr_en[IsprMod]),
    .out_o(ispr_mod_bignum_wdata_intg_blanked)
  );
  // If the blanker is enabled, the output will not carry the correct ECC bits.  This is not
  // a problem because a blanked value should never be written to the register.  If the blanked
  // value is written to the register nonetheless, an integrity error arises.

  logic [WLEN-1:0]                mod_no_intg_d;
  logic [WLEN-1:0]                mod_no_intg_q;
  logic [WLEN-1:0]                mod_no_intg_q_replicated;
  logic [ExtWLEN-1:0]             mod_intg_calc;
  logic [2*BaseWordsPerWLEN-1:0]  mod_intg_err;
  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_mod_words
    prim_secded_inv_39_32_enc i_secded_enc (
      .data_i(mod_no_intg_d[i_word*32+:32]),
      .data_o(mod_intg_calc[i_word*39+:39])
    );
    prim_secded_inv_39_32_dec i_secded_dec (
      .data_i    (mod_intg_q[i_word*39+:39]),
      .data_o    (/* unused because we abort on any integrity error */),
      .syndrome_o(/* unused */),
      .err_o     (mod_intg_err[i_word*2+:2])
    );
    assign mod_no_intg_q[i_word*32+:32] = mod_intg_q[i_word*39+:32];

    always_ff @(posedge clk_i) begin
      if (mod_wr_en[i_word]) begin
        mod_intg_q[i_word*39+:39] <= mod_intg_d[i_word*39+:39];
      end
    end

    always_comb begin
      mod_no_intg_d[i_word*32+:32] = '0;
      unique case (1'b1)
        // Non-encoded inputs have to be encoded before writing to the register.
        sec_wipe_mod_urnd_i: begin
          // In a secure wipe, `urnd_data_i` is written to the register before the zero word.  The
          // ECC bits should not matter between the two writes, but nonetheless we encode
          // `urnd_data_i` so there is no spurious integrity error.
          mod_no_intg_d[i_word*32+:32] = urnd_data_i[i_word*32+:32];
          mod_intg_d[i_word*39+:39]    = mod_intg_calc[i_word*39+:39];
        end
        // Pre-encoded inputs can directly be written to the register.
        default: mod_intg_d[i_word*39+:39] = ispr_mod_bignum_wdata_intg_blanked[i_word*39+:39];
      endcase

      unique case (1'b1)
        ispr_init_i: mod_intg_d[i_word*39+:39] = EccZeroWord;
        ispr_base_wr_en_i[i_word]: begin
          mod_no_intg_d[i_word*32+:32] = ispr_base_wdata_i;
          mod_intg_d[i_word*39+:39]    = mod_intg_calc[i_word*39+:39];
        end
        default: ;
      endcase
    end

    `ASSERT(ModWrSelOneHot, $onehot0({ispr_init_i, ispr_base_wr_en_i[i_word]}))

    assign mod_ispr_wr_en[i_word] = (ispr_addr_i == IsprMod)                          &
                                    (ispr_base_wr_en_i[i_word] | ispr_bignum_wr_en_i) &
                                    ispr_wr_commit_i;

    assign mod_wr_en[i_word] = ispr_init_i            |
                               mod_ispr_wr_en[i_word] |
                               sec_wipe_mod_urnd_i;
  end

  // Replicate the modulus value to match the ELEN
  always_comb begin
    unique case (alu_bignum_predec_i.alu_elen)
      AluElen32:  mod_no_intg_q_replicated = {(WLEN/32){mod_no_intg_q[31:0]}};
      AluElen256: mod_no_intg_q_replicated = mod_no_intg_q;
      default:    mod_no_intg_q_replicated = mod_no_intg_q;
    endcase
  end

  /////////
  // ACC //
  /////////

  assign ispr_acc_wr_en_o   =
    ((ispr_addr_i == IsprAcc) & ispr_bignum_wr_en_i & ispr_wr_commit_i) | ispr_init_i;


  logic [ExtWLEN-1:0] ispr_acc_bignum_wdata_intg_blanked;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(ExtWLEN)) u_ispr_acc_bignum_wdata_intg_blanker (
    .in_i (ispr_bignum_wdata_intg_i),
    .en_i (ispr_bignum_predec_i.ispr_wr_en[IsprAcc]),
    .out_o(ispr_acc_bignum_wdata_intg_blanked)
  );
  // If the blanker is enabled, the output will not carry the correct ECC bits.  This is not
  // a problem because a blanked value should never be used.  If the blanked value is used
  // nonetheless, an integrity error arises.

  assign ispr_acc_wr_data_intg_o = ispr_init_i ? EccWideZeroWord
                                               : ispr_acc_bignum_wdata_intg_blanked;

  // ISPR read data is muxed out in two stages:
  // 1. Select amongst the ISPRs that have no integrity bits. The output has integrity calculated
  //    for it.
  // 2. Select between the ISPRs that have integrity bits and the result of the first stage.

  // Number of ISPRs that have integrity protection
  localparam int NIntgIspr = 2;
  // IDs fpr ISPRs with integrity
  localparam int IsprModIntg = 0;
  localparam int IsprAccIntg = 1;
  // ID representing all ISPRs with no integrity
  localparam int IsprNoIntg = 2;

  logic [NIntgIspr:0] ispr_rdata_intg_mux_sel;
  logic [ExtWLEN-1:0] ispr_rdata_intg_mux_in    [NIntgIspr+1];
  logic [WLEN-1:0]    ispr_rdata_no_intg_mux_in [NIspr];

  // First stage
  // MOD and ACC supply their own integrity so these values are unused
  assign ispr_rdata_no_intg_mux_in[IsprMod] = 0;
  assign ispr_rdata_no_intg_mux_in[IsprAcc] = 0;

  assign ispr_rdata_no_intg_mux_in[IsprRnd]    = rnd_data_i;
  assign ispr_rdata_no_intg_mux_in[IsprUrnd]   = urnd_data_i;
  assign ispr_rdata_no_intg_mux_in[IsprFlags]  = {{(WLEN - (NFlagGroups * FlagsWidth)){1'b0}},
                                                 flags_flattened};
  // SEC_CM: KEY.SIDELOAD
  assign ispr_rdata_no_intg_mux_in[IsprKeyS0L] = sideload_key_shares_i[0][255:0];
  assign ispr_rdata_no_intg_mux_in[IsprKeyS0H] = {{(WLEN - (SideloadKeyWidth - 256)){1'b0}},
                                                  sideload_key_shares_i[0][SideloadKeyWidth-1:256]};
  assign ispr_rdata_no_intg_mux_in[IsprKeyS1L] = sideload_key_shares_i[1][255:0];
  assign ispr_rdata_no_intg_mux_in[IsprKeyS1H] = {{(WLEN - (SideloadKeyWidth - 256)){1'b0}},
                                                  sideload_key_shares_i[1][SideloadKeyWidth-1:256]};

  logic [WLEN-1:0]    ispr_rdata_no_intg;
  logic [ExtWLEN-1:0] ispr_rdata_intg_calc;

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width  (WLEN),
    .Inputs (NIspr)
  ) u_ispr_rdata_no_intg_mux (
    .clk_i,
    .rst_ni,
    .in_i (ispr_rdata_no_intg_mux_in),
    .sel_i(ispr_bignum_predec_i.ispr_rd_en),
    .out_o(ispr_rdata_no_intg)
  );

  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_rdata_enc
    prim_secded_inv_39_32_enc i_secded_enc (
      .data_i(ispr_rdata_no_intg[i_word * 32 +: 32]),
      .data_o(ispr_rdata_intg_calc[i_word * 39 +: 39])
    );
  end

  // Second stage
  assign ispr_rdata_intg_mux_in[IsprModIntg] = mod_intg_q;
  assign ispr_rdata_intg_mux_in[IsprAccIntg] = ispr_acc_intg_i;
  assign ispr_rdata_intg_mux_in[IsprNoIntg]  = ispr_rdata_intg_calc;

  assign ispr_rdata_intg_mux_sel[IsprModIntg] = ispr_bignum_predec_i.ispr_rd_en[IsprMod];
  assign ispr_rdata_intg_mux_sel[IsprAccIntg] = ispr_bignum_predec_i.ispr_rd_en[IsprAcc];

  assign ispr_rdata_intg_mux_sel[IsprNoIntg] =
    |{ispr_bignum_predec_i.ispr_rd_en[IsprKeyS1H:IsprKeyS0L],
      ispr_bignum_predec_i.ispr_rd_en[IsprUrnd],
      ispr_bignum_predec_i.ispr_rd_en[IsprFlags],
      ispr_bignum_predec_i.ispr_rd_en[IsprRnd]};

  // If we're reading from an ISPR we must be using the ispr_rdata_intg_mux
  `ASSERT(IsprRDataIntgMuxSelIfIsprRd_A,
    |ispr_bignum_predec_i.ispr_rd_en |-> |ispr_rdata_intg_mux_sel)

  // If we're reading from MOD or ACC we must not take the read data from the calculated integrity
  // path
  `ASSERT(IsprModMustTakeIntg_A,
    ispr_bignum_predec_i.ispr_rd_en[IsprMod] |-> !ispr_rdata_intg_mux_sel[IsprNoIntg])

  `ASSERT(IsprAccMustTakeIntg_A,
    ispr_bignum_predec_i.ispr_rd_en[IsprAcc] |-> !ispr_rdata_intg_mux_sel[IsprNoIntg])


  prim_onehot_mux #(
    .Width  (ExtWLEN),
    .Inputs (NIntgIspr+1)
  ) u_ispr_rdata_intg_mux (
    .clk_i,
    .rst_ni,
    .in_i (ispr_rdata_intg_mux_in),
    .sel_i(ispr_rdata_intg_mux_sel),
    .out_o(ispr_rdata_intg_o)
  );

  prim_onehot_enc #(
    .OneHotWidth (NIspr)
  ) u_expected_ispr_rd_en_enc (
    .in_i (ispr_addr_i),
    .en_i (ispr_rd_en_i),
    .out_o(expected_ispr_rd_en_onehot)
  );

  assign ispr_wr_en = |{ispr_bignum_wr_en_i, ispr_base_wr_en_i};

  prim_onehot_enc #(
    .OneHotWidth (NIspr)
  ) u_expected_ispr_wr_en_enc (
    .in_i (ispr_addr_i),
    .en_i (ispr_wr_en),
    .out_o(expected_ispr_wr_en_onehot)
  );

  // SEC_CM: CTRL.REDUN
  assign ispr_predec_error_o =
    |{expected_ispr_rd_en_onehot != ispr_bignum_predec_i.ispr_rd_en,
      expected_ispr_wr_en_onehot != ispr_bignum_predec_i.ispr_wr_en};

  ///////////////////////
  // Shifter & Packing //
  ///////////////////////

  logic [8*24-1:0] operand_a_dense;
  logic [8*24-1:0] operand_b_dense;
  logic [WLEN-1:0] operand_a_dense_extended;
  logic [WLEN-1:0] operand_b_dense_extended;
  logic [WLEN-1:0] shifter_operands_upper [2];
  logic [WLEN-1:0] shifter_operands_lower [2];
  logic [WLEN-1:0] shifter_in_upper;
  logic [WLEN-1:0] shifter_in_lower;
  logic [WLEN-1:0] shifter_res;

  // Pack both operands into a 8 * 24-bit dense format by dropping the upper 8 bits per element.
  for (genvar i = 0; i < 8; i++) begin : gen_packing
    assign operand_a_dense[i * 24+:24] = operation_i.operand_a[i * 32+:24];
    assign operand_b_dense[i * 24+:24] = operation_i.operand_b[i * 32+:24];
  end

  // Extend to 256 bits. The lower dense vector is placed at the upper part such that the
  // shifting can operate on the concatenated dense vectors.
  assign operand_a_dense_extended = {64'd0, operand_a_dense};
  assign operand_b_dense_extended = {operand_b_dense, 64'd0};

  // Using onehot MUXs to select between regular inputs and dense representations reduces the
  // overall glitching activity compared to blanking the operands and using predecoded MUXs.
  // Note that the packer may not contain any logic!

  assign shifter_operands_upper[AluShiftOpFull]  = operation_i.operand_a;
  assign shifter_operands_upper[AluShiftOpDense] = operand_a_dense_extended;
  assign shifter_operands_lower[AluShiftOpFull]  = operation_i.operand_b;
  assign shifter_operands_lower[AluShiftOpDense] = operand_b_dense_extended;

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width (WLEN),
    .Inputs(2)
  ) u_shifter_operand_upper_mux (
    .clk_i,
    .rst_ni,
    .in_i (shifter_operands_upper),
    .sel_i(alu_bignum_predec_i.shift_op_a_sel),
    .out_o(shifter_in_upper)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width (WLEN),
    .Inputs(2)
  ) u_shifter_operand_lower_mux (
    .clk_i,
    .rst_ni,
    .in_i (shifter_operands_lower),
    .sel_i(alu_bignum_predec_i.shift_op_b_sel),
    .out_o(shifter_in_lower)
  );

  otbn_vec_shifter u_vec_shifter (
    .clk_i,
    .rst_ni,
    .shifter_in_upper_i(shifter_in_upper),
    .shifter_in_lower_i(shifter_in_lower),
    .shift_direction_i (alu_bignum_predec_i.shift_dir),
    .shift_amt_i       (alu_bignum_predec_i.shift_amt),
    .vector_mask_i     ({8{alu_bignum_predec_i.shift_mask}}),
    .shifter_res_o     (shifter_res)
  );

  // Unpack the shifted result. Zero extend the 24-bit elements from the lower 8*24 bits
  // to 32-bit elements.
  logic [8*24-1:0] unpack_input_blanked;
  logic [WLEN-1:0] unpacked_res;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(8*24)) u_unpack_input_blanker (
    .in_i (shifter_res[8*24-1:0]),
    .en_i (alu_bignum_predec_i.unpack_shifter_en),
    .out_o(unpack_input_blanked)
  );

  for (genvar i = 0; i < 8; i++) begin : gen_unpacking
    assign unpacked_res[i*32+:32] = {8'b0, unpack_input_blanked[i*24+:24]};
  end

  //////////////////
  // Adders X & Y //
  //////////////////

  logic [WLEN-1:0]     adder_x_op_a_blanked, adder_x_op_b_blanked;
  logic [WLEN-1:0]     adder_x_res;
  logic [NVecProc-1:0] adder_x_carries_out;
  logic [WLEN-1:0]     adder_y_op_a_blanked;
  logic [WLEN-1:0]     adder_y_op_shifter_res_blanked;
  logic [WLEN-1:0]     shift_mod_mux_out;
  logic [WLEN-1:0]     x_res_operand_a_mux_out;
  logic                adder_y_carry_0_in;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_adder_x_op_a_blanked (
    .in_i (operation_i.operand_a),
    .en_i (alu_bignum_predec_i.adder_x_en),
    .out_o(adder_x_op_a_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_adder_x_op_b_blanked (
    .in_i (operation_i.operand_b),
    .en_i (alu_bignum_predec_i.adder_x_en),
    .out_o(adder_x_op_b_blanked)
  );

  otbn_vec_adder #(
    .LVLEN(VLEN),
    .LVChunkLEN(VChunkLEN)
  ) u_vec_adder_x (
    .operand_a_i       (adder_x_op_a_blanked),
    .operand_b_i       (adder_x_op_b_blanked),
    .operand_b_invert_i(alu_bignum_predec_i.adder_x_op_b_invert),
    .carries_in_i      (alu_bignum_predec_i.adder_x_carries_in),
    .use_ext_carry_i   ({NVecProc{alu_bignum_predec_i.adder_carry_sel}}),
    .sum_o             (adder_x_res),
    .carries_out_o     (adder_x_carries_out)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_adder_y_op_a_blanked (
    .in_i (operation_i.operand_a),
    .en_i (alu_bignum_predec_i.adder_y_op_a_en),
    .out_o(adder_y_op_a_blanked)
  );

  assign x_res_operand_a_mux_out =
      alu_bignum_predec_i.x_res_operand_a_sel ? adder_x_res : adder_y_op_a_blanked;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_adder_y_op_shifter_blanked (
    .in_i (shifter_res),
    .en_i (alu_bignum_predec_i.adder_y_op_shifter_en),
    .out_o(adder_y_op_shifter_res_blanked)
  );

  // Despite mod_no_intg_q_replicated is not blanked, a regular predecoded MUX is sufficient. The
  // reason is that SW can control the value of MOD to prevent undesirable SCA leakage due to
  // combining MOD and the operand_b of adder Y.
  assign shift_mod_mux_out =
      alu_bignum_predec_i.shift_mod_sel ? adder_y_op_shifter_res_blanked
                                        : mod_no_intg_q_replicated;

  // The carries_in bits are predecoded except the LSB. It cannot be predecoded because its value
  // depends on the actual flag value.
  otbn_vec_adder #(
    .LVLEN(VLEN),
    .LVChunkLEN(VChunkLEN)
  ) u_vec_adder_y (
    .operand_a_i       (x_res_operand_a_mux_out),
    .operand_b_i       (shift_mod_mux_out),
    .operand_b_invert_i(alu_bignum_predec_i.adder_y_op_b_invert),
    .carries_in_i      ({alu_bignum_predec_i.adder_y_carries_top, adder_y_carry_0_in}),
    .use_ext_carry_i   ({NVecProc{alu_bignum_predec_i.adder_carry_sel}}),
    .sum_o             (adder_y_res),
    .carries_out_o     (adder_y_carries_out)
  );

  /////////////////////////////
  // Modulo Result Selection //
  /////////////////////////////
  logic [WLEN-1:0] arithmetic_result;
  logic            arithmetic_result_used_adder_y;

  otbn_mod_result_selector u_mod_result_selector (
    .result_x_i      (adder_x_res),
    .carries_x_i     (adder_x_carries_out),
    .result_y_i      (adder_y_res),
    .carries_y_i     (adder_y_carries_out),
    .is_subtraction_i(alu_bignum_predec_i.mod_is_subtraction),
    // Adder X is exclusively used for modulo instructions
    .is_modulo_i     (alu_bignum_predec_i.adder_x_en),
    .elen_i          (alu_bignum_predec_i.alu_elen),
    .result_o        (arithmetic_result),
    .adder_y_used_o  (arithmetic_result_used_adder_y)
  );

  /////////////////////////////////////////////////
  // Shifter, Adders, Logic & Transposer control //
  /////////////////////////////////////////////////
  logic [NVecProc-1:0] expected_adder_x_carries_in;
  logic                expected_adder_x_op_b_invert;
  logic [NVecProc-2:0] expected_adder_y_carries_top;
  logic                expected_adder_y_op_b_invert;

  logic expected_adder_x_en;
  logic expected_x_res_operand_a_sel;
  logic expected_adder_y_op_a_en;
  logic expected_adder_y_op_shifter_en;

  logic [1:0] expected_shift_op_a_sel;
  logic [1:0] expected_shift_op_b_sel;
  logic       expected_shift_en;
  logic       expected_shift_right;
  logic       expected_shift_mod_sel;
  logic       expected_logic_a_en;
  logic       expected_logic_shifter_en;
  logic [3:0] expected_logic_res_sel;

  logic expected_mod_is_subtraction;
  logic expected_trn_en;
  logic expected_trn_is_trn1;
  logic expected_unpack_shifter_en;

  always_comb begin
    // We use vectorized adders which support 8x32b or 256b elements stored in a WDR. These adders
    // are split into 8 32b processing elements. Thus we have a carry for each processing element.
    // These carries are predecoded except the LSB carry for adder Y as it depends on the flag
    // value.
    expected_adder_x_carries_in  = '0;
    expected_adder_x_op_b_invert = 1'b0;
    expected_adder_y_carries_top = '0;
    adder_y_carry_0_in           = 1'b0;
    expected_adder_y_op_b_invert = 1'b0;
    adder_update_flags_en_raw    = 1'b0;
    logic_update_flags_en_raw    = 1'b0;

    expected_adder_x_en            = 1'b0;
    expected_x_res_operand_a_sel   = 1'b0;
    expected_adder_y_op_a_en       = 1'b0;
    expected_adder_y_op_shifter_en = 1'b0;
    expected_shift_op_a_sel        = '0;
    expected_shift_op_b_sel        = '0;
    expected_shift_en              = 1'b0;
    expected_shift_right           = 1'b0;
    expected_shift_mod_sel         = 1'b1;
    expected_logic_a_en            = 1'b0;
    expected_logic_shifter_en      = 1'b0;
    expected_logic_res_sel         = '0;

    expected_mod_is_subtraction = 1'b0;
    expected_trn_en             = 1'b0;
    expected_trn_is_trn1        = 1'b0;

    expected_unpack_shifter_en = 1'b0;

    unique case (operation_i.op)
      AluOpBignumAdd,
      AluOpBignumAddv: begin
        // Shifter computes B [>>|<<] shift_amt, no shift for vectorized variant.
        // Y computes A + shifter_res
        // X ignored
        expected_adder_y_carries_top = '0;
        adder_y_carry_0_in           = 1'b0;
        expected_adder_y_op_b_invert = 1'b0;

        expected_adder_y_op_shifter_en          = 1'b1;
        expected_adder_y_op_a_en                = 1'b1;
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;

        if (operation_i.op == AluOpBignumAdd) begin
          adder_update_flags_en_raw = 1'b1;
          expected_shift_right      = operation_i.shift_right;
        end
      end
      AluOpBignumAddc: begin
        // Shifter computes B [>>|<<] shift_amt
        // Y computes A + shifter_res + flags.C
        // X ignored
        expected_adder_y_carries_top = '0;
        adder_y_carry_0_in           = selected_flags.C;
        expected_adder_y_op_b_invert = 1'b0;
        adder_update_flags_en_raw    = 1'b1;

        expected_adder_y_op_shifter_en          = 1'b1;
        expected_adder_y_op_a_en                = 1'b1;
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;
        expected_shift_right                    = operation_i.shift_right;
      end
      AluOpBignumAddm,
      AluOpBignumAddvm: begin
        // X computes A + B
        // Y computes adder_x_res - mod = adder_x_res + ~mod + 1
        // Shifter ignored
        // Mod result selector chooses result based on carries of X and Y (whether mod subtraction
        // in Y should be applied or not).
        expected_adder_x_carries_in  = '0;
        expected_adder_x_op_b_invert = 1'b0;
        expected_adder_y_carries_top = operation_i.op == AluOpBignumAddm ? '0 :
                                                                           {(NVecProc-1){1'b1}};
        adder_y_carry_0_in           = 1'b1;
        expected_adder_y_op_b_invert = 1'b1;

        expected_adder_x_en          = 1'b1;
        expected_x_res_operand_a_sel = 1'b1;
        expected_shift_mod_sel       = 1'b0;
      end
      AluOpBignumSub,
      AluOpBignumSubv: begin
        // Shifter computes B [>>|<<] shift_amt, no shift for vectorized variant.
        // Y computes A - shifter_res = A + ~shifter_res + 1
        // X ignored
        expected_adder_y_carries_top   = operation_i.op == AluOpBignumSub ? '0 :
                                                                            {(NVecProc-1){1'b1}};
        adder_y_carry_0_in             = 1'b1;
        expected_adder_y_op_b_invert   = 1'b1;
        expected_adder_y_op_shifter_en = 1'b1;

        expected_adder_y_op_a_en                = 1'b1;
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;

        if (operation_i.op == AluOpBignumSub) begin
          adder_update_flags_en_raw = 1'b1;
          expected_shift_right      = operation_i.shift_right;
        end
      end
      AluOpBignumSubb: begin
        // Shifter computes B [>>|<<] shift_amt
        // Y computes A - shifter_res + ~flags.C = A + ~shifter_res + flags.C
        // X ignored
        expected_adder_y_carries_top   = '0;
        adder_y_carry_0_in             = ~selected_flags.C;
        expected_adder_y_op_b_invert   = 1'b1;
        adder_update_flags_en_raw      = 1'b1;
        expected_adder_y_op_shifter_en = 1'b1;

        expected_adder_y_op_a_en                = 1'b1;
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;
        expected_shift_right                    = operation_i.shift_right;
      end
      AluOpBignumSubm,
      AluOpBignumSubvm: begin
        // X computes A - B = A + ~B + 1
        // Y computes adder_x_res + mod
        // Shifter ignored
        // Mod result selector chooses result based on carry of X (whether subtraction in Y should
        // be applied or not).
        expected_adder_x_carries_in  = operation_i.op == AluOpBignumSubm ? NVecProc'(1) :
                                                                           {NVecProc{1'b1}};
        expected_adder_x_op_b_invert = 1'b1;
        expected_adder_y_carries_top = '0;
        adder_y_carry_0_in           = 1'b0;
        expected_adder_y_op_b_invert = 1'b0;

        expected_adder_x_en          = 1'b1;
        expected_x_res_operand_a_sel = 1'b1;
        expected_shift_mod_sel       = 1'b0;
        expected_mod_is_subtraction  = 1'b1;
      end
      AluOpBignumRshi: begin
        // Shifter computes {A, B} >> shift_amt
        // X, Y ignored
        // Feed blanked shifter output (adder_y_op_shifter_res_blanked) to Y to avoid undesired
        // leakage in the zero flag computation.
        expected_shift_op_a_sel[AluShiftOpFull] = 1'b1;
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;
        expected_shift_right                    = 1'b1;
        // The shifter result is pushed through the logic block to save an input to the result mux.
        // logic operation set to OR.
        expected_logic_shifter_en            = 1'b1;
        expected_logic_res_sel[AluOpLogicOr] = 1'b1;
      end
      AluOpBignumXor,
      AluOpBignumOr,
      AluOpBignumAnd,
      AluOpBignumNot: begin
        // Shift computes one operand for the logical operation
        // X & Y ignored
        // Feed blanked shifter output (adder_y_op_shifter_res_blanked) to Y to avoid undesired
        // leakage in the zero flag computation.
        logic_update_flags_en_raw             = 1'b1;

        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;
        expected_shift_right                    = operation_i.shift_right;
        expected_logic_a_en                     = operation_i.op != AluOpBignumNot;
        expected_logic_shifter_en               = 1'b1;
        expected_logic_res_sel[AluOpLogicXor]   = operation_i.op == AluOpBignumXor;
        expected_logic_res_sel[AluOpLogicOr]    = operation_i.op == AluOpBignumOr;
        expected_logic_res_sel[AluOpLogicAnd]   = operation_i.op == AluOpBignumAnd;
        expected_logic_res_sel[AluOpLogicNot]   = operation_i.op == AluOpBignumNot;
      end
      AluOpBignumTrn1,
      AluOpBignumTrn2: begin
        expected_trn_en      = 1'b1;
        expected_trn_is_trn1 = operation_i.op == AluOpBignumTrn1;
      end
      AluOpBignumShv: begin
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;
        expected_shift_right                    = operation_i.shift_right;
        // The shifter result is pushed through the logic block to save an input to the result mux.
        // logic operation set to OR.
        expected_logic_shifter_en            = 1'b1;
        expected_logic_res_sel[AluOpLogicOr] = 1'b1;
      end
      AluOpBignumPack: begin
        expected_shift_op_a_sel[AluShiftOpDense] = 1'b1;
        expected_shift_op_b_sel[AluShiftOpDense] = 1'b1;
        expected_shift_en                        = 1'b1;
        expected_shift_right                     = 1'b1;
        // The packed result (shifter result) is pushed through the logic block with operand A
        // blanked and the logic operation set to OR.
        expected_logic_shifter_en            = 1'b1;
        expected_logic_res_sel[AluOpLogicOr] = 1'b1;
      end
      AluOpBignumUnpk: begin
        expected_shift_op_a_sel[AluShiftOpFull] = 1'b1;
        expected_shift_op_b_sel[AluShiftOpFull] = 1'b1;
        expected_shift_en                       = 1'b1;
        expected_shift_right                    = 1'b1;
        expected_unpack_shifter_en              = 1'b1;
      end
      // No operation, do nothing.
      AluOpBignumNone: ;
      default: ;
    endcase
  end

  alu_elen_e               expected_alu_elen;
  trn_elen_e               expected_trn_elen;
  logic                    expected_adder_carry_sel;
  logic [$clog2(WLEN)-1:0] expected_shift_amt;
  logic [VChunkLEN-1:0]    expected_shift_mask;
  logic [1:0]              expected_shift_dir;

  assign expected_alu_elen        = operation_i.alu_elen;
  assign expected_trn_elen        = operation_i.trn_elen;
  assign expected_adder_carry_sel = operation_i.adder_carry_sel;
  assign expected_shift_amt       = operation_i.shift_amt;
  assign expected_shift_mask      = operation_i.shift_mask;

  assign expected_shift_dir[AluShiftDirLeft]  = expected_shift_en &
                                                !expected_shift_right;
  assign expected_shift_dir[AluShiftDirRight] = expected_shift_en &
                                                expected_shift_right;

  // SEC_CM: CTRL.REDUN
  assign alu_predec_error_o =
    |{expected_adder_x_carries_in != alu_bignum_predec_i.adder_x_carries_in,
      expected_adder_x_op_b_invert != alu_bignum_predec_i.adder_x_op_b_invert,
      expected_adder_y_carries_top != alu_bignum_predec_i.adder_y_carries_top,
      expected_adder_y_op_b_invert != alu_bignum_predec_i.adder_y_op_b_invert,
      expected_adder_x_en != alu_bignum_predec_i.adder_x_en,
      expected_x_res_operand_a_sel != alu_bignum_predec_i.x_res_operand_a_sel,
      expected_adder_y_op_a_en != alu_bignum_predec_i.adder_y_op_a_en,
      expected_adder_y_op_shifter_en != alu_bignum_predec_i.adder_y_op_shifter_en,
      expected_shift_op_a_sel != alu_bignum_predec_i.shift_op_a_sel,
      expected_shift_op_b_sel != alu_bignum_predec_i.shift_op_b_sel,
      expected_shift_dir != alu_bignum_predec_i.shift_dir,
      expected_shift_amt != alu_bignum_predec_i.shift_amt,
      expected_shift_mod_sel != alu_bignum_predec_i.shift_mod_sel,
      expected_logic_a_en != alu_bignum_predec_i.logic_a_en,
      expected_logic_shifter_en != alu_bignum_predec_i.logic_shifter_en,
      expected_logic_res_sel != alu_bignum_predec_i.logic_res_sel,
      expected_flag_group_sel != alu_bignum_predec_i.flag_group_sel,
      expected_flag_sel != alu_bignum_predec_i.flag_sel,
      expected_flags_keep != alu_bignum_predec_i.flags_keep,
      expected_flags_adder_update != alu_bignum_predec_i.flags_adder_update,
      expected_flags_logic_update != alu_bignum_predec_i.flags_logic_update,
      expected_flags_mac_update != alu_bignum_predec_i.flags_mac_update,
      expected_flags_ispr_wr != alu_bignum_predec_i.flags_ispr_wr,
      expected_alu_elen != alu_bignum_predec_i.alu_elen,
      expected_trn_elen != alu_bignum_predec_i.trn_elen,
      expected_adder_carry_sel != alu_bignum_predec_i.adder_carry_sel,
      expected_mod_is_subtraction != alu_bignum_predec_i.mod_is_subtraction,
      expected_shift_mask != alu_bignum_predec_i.shift_mask,
      expected_trn_en != alu_bignum_predec_i.trn_en,
      expected_trn_is_trn1 != alu_bignum_predec_i.trn_is_trn1,
      expected_unpack_shifter_en != alu_bignum_predec_i.unpack_shifter_en};

  ////////////////////////
  // Logical operations //
  ////////////////////////

  logic [WLEN-1:0] logical_res_mux_in [4];
  logic [WLEN-1:0] logical_op_a_blanked;
  logic [WLEN-1:0] logical_op_shifter_res_blanked;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_logical_op_a_blanker (
    .in_i (operation_i.operand_a),
    .en_i (alu_bignum_predec_i.logic_a_en),
    .out_o(logical_op_a_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_logical_op_shifter_res_blanker (
    .in_i (shifter_res),
    .en_i (alu_bignum_predec_i.logic_shifter_en),
    .out_o(logical_op_shifter_res_blanked)
  );

  assign logical_res_mux_in[AluOpLogicXor] = logical_op_a_blanked ^ logical_op_shifter_res_blanked;
  assign logical_res_mux_in[AluOpLogicOr]  = logical_op_a_blanked | logical_op_shifter_res_blanked;
  assign logical_res_mux_in[AluOpLogicAnd] = logical_op_a_blanked & logical_op_shifter_res_blanked;
  assign logical_res_mux_in[AluOpLogicNot] = ~logical_op_shifter_res_blanked;

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width (WLEN),
    .Inputs(4)
  ) u_logical_res_mux (
    .clk_i,
    .rst_ni,
    .in_i (logical_res_mux_in),
    .sel_i(alu_bignum_predec_i.logic_res_sel),
    .out_o(logical_res)
  );

  ///////////////////////
  // Vector Transposer //
  ///////////////////////

  logic [WLEN-1:0] vec_transposer_op_a_blanked;
  logic [WLEN-1:0] vec_transposer_op_b_blanked;
  logic [WLEN-1:0] vec_transposer_res;

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_vec_transposer_op_a_blanker (
    .in_i (operation_i.operand_a),
    .en_i (alu_bignum_predec_i.trn_en),
    .out_o(vec_transposer_op_a_blanked)
  );

  // SEC_CM: DATA_REG_SW.SCA
  prim_blanker #(.Width(WLEN)) u_vec_transposer_op_b_blanker (
    .in_i (operation_i.operand_b),
    .en_i (alu_bignum_predec_i.trn_en),
    .out_o(vec_transposer_op_b_blanked)
  );

  otbn_vec_transposer u_vec_transposer (
    .clk_i,
    .rst_ni,
    .operand_a_i(vec_transposer_op_a_blanked),
    .operand_b_i(vec_transposer_op_b_blanked),
    .is_trn1_i  (alu_bignum_predec_i.trn_is_trn1),
    .elen_i     (alu_bignum_predec_i.trn_elen),
    .result_o   (vec_transposer_res)
  );

  ////////////////////////
  // Output multiplexer //
  ////////////////////////
  // Due to the blanking only one input to the output multiplexer is non zero at the same time.
  // This allows to implement the selection with one large OR instead of a regular mux.
  // Note, the shifter result is pushed through the logic block. Similarly is the non modulo result
  // pushed through the modulo result selector.
  assign operation_result_o = arithmetic_result | unpacked_res | logical_res | vec_transposer_res;

  `ASSERT(OnlyOneResultActive_A,
          $onehot0({|arithmetic_result,
                    |unpacked_res,
                    |logical_res,
                    |vec_transposer_res}),
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // We need to generate a signal indicating whether we have used the value of the MOD WSR and thus
  // need to check its integrity. See otbn_mod_result_selector for more details.
  logic adder_y_res_used;
  always_comb begin
    unique case(operation_i.op)
      AluOpBignumAdd,
      AluOpBignumAddv,
      AluOpBignumAddc,
      AluOpBignumSub,
      AluOpBignumSubv,
      AluOpBignumSubb,
      AluOpBignumAddm,
      AluOpBignumAddvm,
      AluOpBignumSubm,
      AluOpBignumSubvm: adder_y_res_used = arithmetic_result_used_adder_y;

      AluOpBignumRshi,
      AluOpBignumXor,
      AluOpBignumOr,
      AluOpBignumAnd,
      AluOpBignumNot,
      AluOpBignumTrn1,
      AluOpBignumTrn2,
      AluOpBignumShv,
      AluOpBignumPack,
      AluOpBignumUnpk: adder_y_res_used = 1'b0;
      // Most arithmetic operations use the adder Y result, so mark it as used as save default.
      default:         adder_y_res_used = 1'b1;
    endcase
  end

  // Tie off unused signals.
  logic unused_operation_commit;
  assign unused_operation_commit = operation_commit_i;

  // Determine if `mod_intg_q` is used.  The control signals are only valid if `operation_i.op` is
  // not none. If `shift_mod_sel` is low, `mod_intg_q` flows into `adder_y_op_b` and from there
  // into `adder_y_res`.  In this case, `mod_intg_q` is used iff  `adder_y_res` flows into
  // `operation_result_o`.
  logic mod_used;
  assign mod_used = operation_valid_i & (operation_i.op != AluOpBignumNone) &
                    !alu_bignum_predec_i.shift_mod_sel & adder_y_res_used;
  `ASSERT_KNOWN(ModUsed_A, mod_used)

  // Raise a register integrity violation error iff `mod_intg_q` is used and (at least partially)
  // invalid.
  assign reg_intg_violation_err_o = mod_used & |(mod_intg_err);
  `ASSERT_KNOWN(RegIntgErrKnown_A, reg_intg_violation_err_o)

  // Detect and signal unexpected secure wipe signals.
  assign sec_wipe_err_o = sec_wipe_mod_urnd_i & ~sec_wipe_running_i;

  // Blanking Assertions
  // All blanking assertions are reset with predec_error or overall error in the whole system
  // -indicated by operation_commit_i port- as OTBN does not guarantee blanking in the case
  // of an error.

  // adder_x_res related blanking
  `ASSERT(BlankingBignumAluXOp_A,
          !expected_adder_x_en
          |-> {adder_x_op_a_blanked, adder_x_op_b_blanked, adder_x_res, adder_x_carries_out} == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // adder_y_res related blanking
  `ASSERT(BlankingBignumAluYOpA_A,
          !expected_adder_y_op_a_en |-> adder_y_op_a_blanked == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)
  `ASSERT(BlankingBignumAluYOpShft_A,
          !expected_adder_y_op_shifter_en |-> adder_y_op_shifter_res_blanked == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // Adder Y must be blanked when its result is not used, with one exception: For `BN.SUBM` and
  // `BN.SUBVM` with `a >= b` (thus the result of Adder X has the carry bit set), the result of
  // Adder Y is not used but it cannot be blanked solely based on the carry bit.
  `ASSERT(BlankingBignumAluYResUsed_A,
          !adder_y_res_used &&
          !((operation_i.op == AluOpBignumSubm || operation_i.op == AluOpBignumSubvm)
            && !arithmetic_result_used_adder_y)
          |-> {x_res_operand_a_mux_out, shift_mod_mux_out} == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // shifter_res related blanking
  `ASSERT(BlankingBignumAluShftA_A,
          (expected_shift_op_a_sel == '0) |-> shifter_in_upper == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  `ASSERT(BlankingBignumAluShftB_A,
          (expected_shift_op_b_sel == '0) |-> shifter_in_lower == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  `ASSERT(BlankingBignumAluShftRes_A,
          (expected_shift_op_a_sel == '0) && (expected_shift_op_b_sel == '0) |-> shifter_res == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // logical_res related blanking
  `ASSERT(BlankingBignumAluLogicOpA_A,
          !expected_logic_a_en |-> logical_op_a_blanked == '0,
          clk_i, !rst_ni || alu_predec_error_o  || !operation_commit_i)

  `ASSERT(BlankingBignumAluLogicShft_A,
          !expected_logic_shifter_en |-> logical_op_shifter_res_blanked == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  `ASSERT(BlankingBignumAluLogicRes_A,
          !(expected_logic_a_en || expected_logic_shifter_en) |-> logical_res == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // Vector transposer related blanking
  `ASSERT(BlankingBignumAluVecTrn_A,
          !expected_trn_en
          |-> {vec_transposer_op_a_blanked, vec_transposer_op_b_blanked} == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // Vector unpack related blanking
  `ASSERT(BlankingBignumAluVecUnpk_A,
          !(expected_unpack_shifter_en) |-> unpacked_res == '0,
          clk_i, !rst_ni || alu_predec_error_o || !operation_commit_i)

  // MOD ISPR Blanking
  `ASSERT(BlankingIsprMod_A,
          !(|mod_wr_en) |-> ispr_mod_bignum_wdata_intg_blanked == '0,
          clk_i, !rst_ni || ispr_predec_error_o || alu_predec_error_o || !operation_commit_i)

  // ACC ISPR Blanking
  `ASSERT(BlankingIsprACC_A,
          !(|ispr_acc_wr_en_o) |-> ispr_acc_bignum_wdata_intg_blanked == '0,
          clk_i, !rst_ni || ispr_predec_error_o || alu_predec_error_o || !operation_commit_i)

endmodule
