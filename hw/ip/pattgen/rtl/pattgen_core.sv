// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// pattgen core implementation

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

  // TODO: to be replaced later by true rtl
  localparam DataWidth = 4;
  localparam NumGates  = 1000;

  logic [DataWidth-1:0] data_i;
  logic [DataWidth-1:0] data_o;
  logic valid_i;
  logic valid_o;

  assign valid_i    = reg2hw.start.start0 | reg2hw.start.start1;
  assign data_i[0]  = reg2hw.patt_len.len0[0];
  assign data_i[1]  = reg2hw.patt_len.len1[0];
  assign data_i[2]  = reg2hw.patt_loop.loop0[0];
  assign data_i[3]  = reg2hw.patt_loop.loop1[0];

  // TODO: pseudo-logic 1kGE is added
  prim_gate_gen  #(
    .DataWidth ( DataWidth ),
    .NumGates  ( NumGates  )
  ) prim_gate_gen (
    .clk_i     (clk_i   ),
    .rst_ni    (rst_ni  ),
    .valid_i   (valid_i ),
    .data_i    (data_i  ),
    .data_o    (data_o  ),
    .valid_o   (valid_o )
  );

  assign  pda0_tx         = data_o[0];
  assign  pcl0_tx         = data_o[1];
  assign  pda1_tx         = data_o[2];
  assign  pcl1_tx         = data_o[3];
  assign  intr_patt_done0 = valid_o | data_o[1];
  assign  intr_patt_done1 = valid_o ^ data_o[0];

endmodule : pattgen_core
