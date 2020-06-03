// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// patt core implementation

module pattgen_core (
  input  clk_i,
  input  rst_ni,
  input  pattgen_reg_pkg::pattgen_reg2hw_t  reg2hw,
  output pattgen_reg_pkg::pattgen_hw2reg_t  hw2reg,

  output logic  pda0_tx,
  output logic  pcl0_tx,
  output logic  pda1_tx,
  output logic  pcl1_tx,

  output logic  intr_patt_done0,
  output logic  intr_patt_done1
);

  // TODO
  assign  pda0_tx = 1'b0;
  assign  pcl0_tx = 1'b0;
  assign  pda1_tx = 1'b0;
  assign  pcl1_tx = 1'b0;
  assign  intr_patt_done0 = 1'b0;
  assign  intr_patt_done1 = 1'b0;

endmodule : pattgen_core
