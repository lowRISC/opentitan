// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * 256b General Purpose Register File (GPRs) with integrity code detecting triple bit errors on a
 * 32-bit granule (312 bits total).
 *
 * This wraps two implementations, one for FPGA (otbn_rf_base_fpga) implementation the other for
 * ASIC (otbn_rf_base_ff).
 *
 * Integrity protection uses an inverted (39, 32) Hsaio code providing a Hamming distance of 4.
 *
 * `wr_data_no_intg_i` supplies data that requires integrity calulation and `wr_data_intg_i`
 * supplies data that comes with integrity. `wr_data_intg_sel_i` is asserted to select the data with
 * integrity for the write, otherwise integrity is calculated separately from `wr_data_i`.
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 * - triple error detection
 */

module otbn_rf_bignum
  import otbn_pkg::*;
#(
  // Register file implementation selection, see otbn_pkg.sv.
  parameter regfile_e RegFile = RegFileFF
)(
  input  logic                   clk_i,
  input  logic                   rst_ni,

  input  logic [WdrAw-1:0]       wr_addr_i,
  input  logic [1:0]             wr_en_i,
  input  logic                   wr_commit_i,
  input  logic [WLEN-1:0]        wr_data_no_intg_i,
  input  logic [ExtWLEN-1:0]     wr_data_intg_i,
  input  logic                   wr_data_intg_sel_i,

  input  logic                   rd_en_a_i,
  input  logic [WdrAw-1:0]       rd_addr_a_i,
  output logic [ExtWLEN-1:0]     rd_data_a_intg_o,

  input  logic                   rd_en_b_i,
  input  logic [WdrAw-1:0]       rd_addr_b_i,
  output logic [ExtWLEN-1:0]     rd_data_b_intg_o,

  output logic                   intg_err_o,

  input  rf_predec_bignum_t      rf_predec_bignum_i,
  output logic                   predec_error_o,

  output logic                   spurious_we_err_o
);

  logic [ExtWLEN-1:0]            wr_data_intg_mux_out, wr_data_intg_calc;
  logic [1:0]                    wr_en_internal;
  logic [BaseWordsPerWLEN*2-1:0] rd_data_a_err, rd_data_b_err;
  logic [NWdr-1:0]               expected_rd_en_a_onehot, expected_rd_en_b_onehot;
  logic [NWdr-1:0]               expected_wr_en_onehot;
  logic                          rd_en_a_mismatch, rd_en_b_mismatch, wr_en_mismatch;

  assign wr_en_internal = wr_en_i & {2{wr_commit_i}};

  if (RegFile == RegFileFF) begin : gen_rf_bignum_ff
    otbn_rf_bignum_ff u_otbn_rf_bignum_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i(wr_en_internal),
      .wr_data_i(wr_data_intg_mux_out),

      .rd_addr_a_i,
      .rd_data_a_o(rd_data_a_intg_o),

      .rd_addr_b_i,
      .rd_data_b_o(rd_data_b_intg_o),

      .rf_predec_bignum_i,

      .we_err_o(spurious_we_err_o)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_rf_bignum_fpga
    otbn_rf_bignum_fpga #(
      .WordZeroVal(prim_secded_pkg::SecdedInv3932ZeroWord)
    ) u_otbn_rf_bignum_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i(wr_en_internal),
      .wr_data_i(wr_data_intg_mux_out),

      .rd_addr_a_i,
      .rd_data_a_o(rd_data_a_intg_o),

      .rd_addr_b_i,
      .rd_data_b_o(rd_data_b_intg_o),

      .we_err_o(spurious_we_err_o)
    );
  end

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) u_rf_ren_a_onehot_enc (
    .in_i  (rd_addr_a_i),
    .en_i  (rd_en_a_i),
    .out_o (expected_rd_en_a_onehot)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) u_rf_ren_b_onehot_enc (
    .in_i  (rd_addr_b_i),
    .en_i  (rd_en_b_i),
    .out_o (expected_rd_en_b_onehot)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) u_rf_we_onehot_enc (
    .in_i  (wr_addr_i),
    .en_i  (|wr_en_i),
    .out_o (expected_wr_en_onehot)
  );

  // SEC_CM: CTRL.REDUN
  assign rd_en_a_mismatch = expected_rd_en_a_onehot != rf_predec_bignum_i.rf_ren_a;
  assign rd_en_b_mismatch = expected_rd_en_b_onehot != rf_predec_bignum_i.rf_ren_b;
  assign wr_en_mismatch   = expected_wr_en_onehot   != rf_predec_bignum_i.rf_we;

  assign predec_error_o = rd_en_a_mismatch | rd_en_b_mismatch | wr_en_mismatch;

  // New data can have its integrity from an external source or the integrity can be calculated here
  assign wr_data_intg_mux_out = wr_data_intg_sel_i ? wr_data_intg_i : wr_data_intg_calc;

  // SEC_CM: RF_BIGNUM.DATA_REG_SW.INTEGRITY
  // Separate integrity encode and decode per 32-bit integrity granule
  for (genvar i = 0; i < BaseWordsPerWLEN; ++i) begin : g_rf_intg_calc
    prim_secded_inv_39_32_enc u_wr_data_intg_enc (
      .data_i(wr_data_no_intg_i[i * 32 +: 32]),
      .data_o(wr_data_intg_calc[i * 39 +: 39])
    );

    // Integrity decoders used to detect errors only, corrections (`syndrome_o`/`d_o`) are ignored
    prim_secded_inv_39_32_dec u_rd_data_a_intg_dec (
      .data_i    (rd_data_a_intg_o[i * 39 +: 39]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rd_data_a_err[i*2 +: 2])
    );

    prim_secded_inv_39_32_dec u_rd_data_b_intg_dec (
      .data_i    (rd_data_b_intg_o[i * 39 +: 39]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rd_data_b_err[i*2 +: 2])
    );
  end

  logic intg_err_unbuf, intg_err_buf;

  assign intg_err_unbuf = ((|rd_data_a_err) & rd_en_a_i) |
                          ((|rd_data_b_err) & rd_en_b_i);

  // This primitive is used to place a constraint for synthesis. It is required to
  // ensure that the signal name will be available in the synthesized netlist.
  prim_buf #(
    .Width(1)
  ) u_prim_buf (
    .in_i(intg_err_unbuf),
    .out_o(intg_err_buf)
  );

  assign intg_err_o = intg_err_buf;

  `ASSERT(BlankingBignumRegReadA_A,
          !rd_en_a_i |->  rd_data_a_intg_o == '0,
          clk_i, !rst_ni || predec_error_o || !wr_commit_i)

  `ASSERT(BlankingBignumRegReadB_A,
          !rd_en_b_i |->  rd_data_b_intg_o == '0,
          clk_i, !rst_ni || predec_error_o || !wr_commit_i)

  // Make sure we're not outputting X. This indicates that something went wrong during the initial
  // secure wipe.
  `ASSERT(OtbnRfBignumRdAKnown, rd_en_a_i && !rd_en_a_mismatch |-> !$isunknown(rd_data_a_intg_o))
  `ASSERT(OtbnRfBignumRdBKnown, rd_en_b_i && !rd_en_b_mismatch |-> !$isunknown(rd_data_b_intg_o))
endmodule
