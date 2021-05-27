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
  input  logic               clk_i,
  input  logic               rst_ni,

  input  logic [WdrAw-1:0]   wr_addr_i,
  input  logic [1:0]         wr_en_i,
  input  logic [WLEN-1:0]    wr_data_no_intg_i,
  input  logic [ExtWLEN-1:0] wr_data_intg_i,
  input  logic               wr_data_intg_sel_i,

  input  logic               rd_en_a_i,
  input  logic [WdrAw-1:0]   rd_addr_a_i,
  output logic [ExtWLEN-1:0] rd_data_a_intg_o,

  input  logic               rd_en_b_i,
  input  logic [WdrAw-1:0]   rd_addr_b_i,
  output logic [ExtWLEN-1:0] rd_data_b_intg_o,

  output logic               rd_data_err_o
);

  logic [ExtWLEN-1:0]            wr_data_intg_mux_out, wr_data_intg_calc;
  logic [BaseWordsPerWLEN*2-1:0] rd_data_a_err, rd_data_b_err;

  if (RegFile == RegFileFF) begin : gen_rf_bignum_ff
    otbn_rf_bignum_ff u_otbn_rf_bignum_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i,
      .wr_data_i(wr_data_intg_mux_out),

      .rd_addr_a_i,
      .rd_data_a_o(rd_data_a_intg_o),

      .rd_addr_b_i,
      .rd_data_b_o(rd_data_b_intg_o)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_rf_bignum_fpga
    otbn_rf_bignum_fpga u_otbn_rf_bignum_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i,
      .wr_data_i(wr_data_intg_mux_out),

      .rd_addr_a_i,
      .rd_data_a_o(rd_data_a_intg_o),

      .rd_addr_b_i,
      .rd_data_b_o(rd_data_b_intg_o)
    );
  end

  // New data can have its integrity from an external source or the integrity can be calculated here
  assign wr_data_intg_mux_out = wr_data_intg_sel_i ? wr_data_intg_i : wr_data_intg_calc;

  // Separate integrity encode and decode per 32-bit integrity granule
  for (genvar i = 0; i < BaseWordsPerWLEN; ++i) begin : g_rf_intg_calc
    prim_secded_39_32_enc u_wr_data_intg_enc (
      .data_i(wr_data_no_intg_i[i * 32 +: 32]),
      .data_o(wr_data_intg_calc[i * 39 +: 39])
    );

    // Integrity decoders used to detect errors only, corrections (`syndrome_o`/`d_o`) are ignored
    prim_secded_39_32_dec u_rd_data_a_intg_dec (
      .data_i    (rd_data_a_intg_o[i * 39 +: 39]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rd_data_a_err[i*2 +: 2])
    );

    prim_secded_39_32_dec u_rd_data_b_intg_dec (
      .data_i    (rd_data_b_intg_o[i * 39 +: 39]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rd_data_b_err[i*2 +: 2])
    );
  end

  assign rd_data_err_o = ((|rd_data_a_err) & rd_en_a_i) | ((|rd_data_b_err) & rd_en_b_i);
endmodule
