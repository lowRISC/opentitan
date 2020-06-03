// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// PATTGEN implementation

`include "prim_assert.sv"

module pattgen (
  input  clk_i,
  input  rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  output logic  pda0_tx_o,
  output logic  pcl0_tx_o,
  output logic  pda1_tx_o,
  output logic  pcl1_tx_o,

  output logic  intr_patt_done0_o,
  output logic  intr_patt_done1_o
);

  import pattgen_reg_pkg::*;

  pattgen_reg2hw_t reg2hw;
  pattgen_hw2reg_t hw2reg;

  // Register
  pattgen_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i (1'b0)
  );

	// Pattgen core
  pattgen_core pattgen_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .pda0_tx(pda0_tx_o),
    .pcl0_tx(pcl0_tx_o),
    .pda1_tx(pda1_tx_o),
    .pcl1_tx(pcl1_tx_o),

    .intr_patt_done0(intr_patt_done0_o),
    .intr_patt_done1(intr_patt_done1_o)
  );

  // Assertion
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAValidKnown, tl_o.a_ready)
  `ASSERT_KNOWN(Pda1TxKnownO, pda0_tx_o)
  `ASSERT_KNOWN(Pcl1TxKnownO, pcl0_tx_o)
  `ASSERT_KNOWN(Pda2TxKnownO, pda1_tx_o)
  `ASSERT_KNOWN(Pcl2TxKnownO, pcl1_tx_o)
  `ASSERT_KNOWN(IntrPattDone1KnownO, intr_patt_done0_o)
  `ASSERT_KNOWN(IntrPattDone2KnownO, intr_patt_done1_o)
endmodule : pattgen
