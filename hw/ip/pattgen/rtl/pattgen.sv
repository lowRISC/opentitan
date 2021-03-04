// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module pattgen
  import pattgen_reg_pkg::*;
(
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  output logic cio_pda0_tx_o,
  output logic cio_pcl0_tx_o,
  output logic cio_pda1_tx_o,
  output logic cio_pcl1_tx_o,
  output logic cio_pda0_tx_en_o,
  output logic cio_pcl0_tx_en_o,
  output logic cio_pda1_tx_en_o,
  output logic cio_pcl1_tx_en_o,

  output logic intr_done_ch0_o,
  output logic intr_done_ch1_o
);

  pattgen_reg2hw_t reg2hw;
  pattgen_hw2reg_t hw2reg;

  pattgen_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  assign cio_pda0_tx_en_o = 1'b1;
  assign cio_pcl0_tx_en_o = 1'b1;
  assign cio_pda1_tx_en_o = 1'b1;
  assign cio_pcl1_tx_en_o = 1'b1;

  pattgen_core u_pattgen_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .pda0_tx_o(cio_pda0_tx_o),
    .pcl0_tx_o(cio_pcl0_tx_o),
    .pda1_tx_o(cio_pda1_tx_o),
    .pcl1_tx_o(cio_pcl1_tx_o),

    .intr_done_ch0_o,
    .intr_done_ch1_o
  );

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(Pcl0TxKnownO_A, cio_pcl0_tx_o)
  `ASSERT_KNOWN(Pda0TxKnownO_A, cio_pda0_tx_o)
  `ASSERT_KNOWN(Pcl1TxKnownO_A, cio_pcl1_tx_o)
  `ASSERT_KNOWN(Pda1TxKnownO_A, cio_pda1_tx_o)
  `ASSERT_KNOWN(Pcl0TxEnKnownO_A, cio_pcl0_tx_en_o)
  `ASSERT_KNOWN(Pda0TxEnKnownO_A, cio_pda0_tx_en_o)
  `ASSERT_KNOWN(Pcl1TxEnKnownO_A, cio_pcl1_tx_en_o)
  `ASSERT_KNOWN(Pda1TxEnKnownO_A, cio_pda1_tx_en_o)
  `ASSERT_KNOWN(IntrCh0DoneKnownO_A, intr_done_ch0_o)
  `ASSERT_KNOWN(IntrCh1DoneKnownO_A, intr_done_ch1_o)

endmodule : pattgen
