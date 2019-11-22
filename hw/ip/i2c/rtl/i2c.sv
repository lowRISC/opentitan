// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C top level wrapper file

module i2c (
  input                     clk_i,
  input                     rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Generic IO
  input                     cio_scl_i,
  output logic              cio_scl_o,
  output logic              cio_scl_en_o,
  input                     cio_sda_i,
  output logic              cio_sda_o,
  output logic              cio_sda_en_o,

  // Interrupts
  output logic              intr_fmt_watermark_o,
  output logic              intr_rx_watermark_o,
  output logic              intr_fmt_overflow_o,
  output logic              intr_rx_overflow_o,
  output logic              intr_nak_o,
  output logic              intr_scl_interference_o,
  output logic              intr_sda_interference_o,
  output logic              intr_stretch_timeout_o,
  output logic              intr_sda_unstable_o
);

  import i2c_reg_pkg::*;

  i2c_reg2hw_t reg2hw;
  i2c_hw2reg_t hw2reg;

  i2c_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  logic scl_int;
  logic sda_int;

  i2c_core i2c_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .scl_i(cio_scl_i),
    .scl_o(scl_int),
    .sda_i(cio_sda_i),
    .sda_o(sda_int),

    .intr_fmt_watermark_o,
    .intr_rx_watermark_o,
    .intr_fmt_overflow_o,
    .intr_rx_overflow_o,
    .intr_nak_o,
    .intr_scl_interference_o,
    .intr_sda_interference_o,
    .intr_stretch_timeout_o,
    .intr_sda_unstable_o
  );

  // For I2C, in standard, fast and fast-plus modes, outputs simulated as open-drain outputs.
  // Asserting scl or sda high should be equivalent to a tri-state output.
  // The output, when enabled, should only assert low.

  assign cio_scl_o = 1'b0;
  assign cio_sda_o = 1'b0;

  assign cio_scl_en_o = ~scl_int;
  assign cio_sda_en_o = ~sda_int;

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid, clk_i, !rst_ni)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready, clk_i, !rst_ni)
  `ASSERT_KNOWN(CioSclKnownO_A, cio_scl_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(CioSclEnKnownO_A, cio_scl_en_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(CioSdaKnownO_A, cio_sda_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(CioSdaEnKnownO_A, cio_sda_en_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrFmtWtmkKnownO_A, intr_fmt_watermark_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrRxWtmkKnownO_A, intr_rx_watermark_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrFmtOflwKnownO_A, intr_fmt_overflow_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrRxOflwKnownO_A, intr_rx_overflow_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrNakKnownO_A, intr_nak_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrSclInterfKnownO_A, intr_scl_interference_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrSdaInterfKnownO_A, intr_sda_interference_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrStretchTimeoutKnownO_A, intr_stretch_timeout_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IntrSdaUnstableKnownO_A, intr_sda_unstable_o, clk_i, !rst_ni)

endmodule
