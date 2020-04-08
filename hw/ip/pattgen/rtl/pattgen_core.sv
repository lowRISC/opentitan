// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// patt core implementation

module patt_core (
  input                             clk_i,
  input                             rst_ni,
  input i2c_reg_pkg::i2c_reg2hw_t   reg2hw,
  output i2c_reg_pkg::i2c_hw2reg_t  hw2reg,

  output logic                      pda1_tx,
  output logic                      pcl1_tx,
  output logic                      pda2_tx,
  output logic                      pcl2_tx,

  output logic                      intr_patt_done1,
  output logic                      intr_patt_done2
);

  // TODO
  assign  pda1_tx = 1'b0;
  assign  pcl1_tx = 1'b0;
  assign  pda2_tx = 1'b0;
  assign  pcl2_tx = 1'b0;
  assign  intr_patt_done1 = 1'b0;
  assign  intr_patt_done2 = 1'b0;

endmodule