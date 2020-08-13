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

  output logic  pda0_tx_o,
  output logic  pcl0_tx_o,
  output logic  pda1_tx_o,
  output logic  pcl1_tx_o,

  output logic  intr_patt_done_ch0_o,
  output logic  intr_patt_done_ch1_o
);

  // TODO: to be replaced later by true rtl
  localparam DataWidth = 32;
  // use less than estimated 1K due to glue logics
  localparam NumGates  = 800;

  logic [DataWidth-1:0] data_i;
  logic [DataWidth-1:0] data_o;
  logic data_ch0, data_ch1;
  logic prediv_ch0, prediv_ch1;

  logic valid_o;
  logic valid_i;
  logic event_intr_patt_done_ch0;
  logic event_intr_patt_done_ch1;


  assign data_ch0   = &(reg2hw.patt_data_ch0[0].q | reg2hw.patt_data_ch0[1].q) &
                      reg2hw.patt_data_ch0[0].qe & reg2hw.patt_data_ch0[1].qe;
  assign data_ch1   = &(reg2hw.patt_data_ch1[0].q | reg2hw.patt_data_ch1[1].q) &
                      reg2hw.patt_data_ch1[0].qe & reg2hw.patt_data_ch1[1].qe;

  assign prediv_ch0 = (&reg2hw.patt_prediv[0].q)  | reg2hw.patt_prediv[0].qe;
  assign prediv_ch1 = (&reg2hw.patt_prediv[1].q)  | reg2hw.patt_prediv[1].qe;

  assign valid_i   = (reg2hw.patt_start.ch0_start.q & reg2hw.patt_start.ch0_start.qe) |
                     (reg2hw.patt_start.ch1_start.q & reg2hw.patt_start.ch1_start.qe) &
                     reg2hw.patt_ctrl.q;

  assign data_i[0] = (^reg2hw.patt_len.ch0_len.q)   & reg2hw.patt_len.ch0_len.qe;
  assign data_i[1] = (^reg2hw.patt_len.ch1_len.q)   & reg2hw.patt_len.ch1_len.qe;
  assign data_i[2] = (|reg2hw.patt_loop.ch0_loop.q) & reg2hw.patt_loop.ch0_loop.qe;
  assign data_i[3] = (|reg2hw.patt_loop.ch1_loop.q) & reg2hw.patt_loop.ch1_loop.qe;
  assign data_i[4] = data_ch0;
  assign data_i[5] = data_ch1;
  assign data_i[6] = prediv_ch0;
  assign data_i[7] = prediv_ch1;
  assign data_i[13:8]  = {6{data_ch0}};
  assign data_i[19:14] = {6{data_ch1}};
  assign data_i[25:20] = {6{prediv_ch0}};
  assign data_i[31:26] = {6{prediv_ch1}};

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

  assign pda0_tx_o       = ^data_o;
  assign pcl0_tx_o       = ~|data_o;
  assign pda1_tx_o       = ~&data_o;
  assign pcl1_tx_o       = &data_o;

  assign event_intr_patt_done_ch0 = valid_o | (^data_o);
  assign event_intr_patt_done_ch1 = valid_o ^ (&data_o);

  prim_intr_hw #(.Width(1)) intr_hw_intr_patt_done_ch0_o (
    .event_intr_i           (event_intr_patt_done_ch0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.intr_patt_done_ch0.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.intr_patt_done_ch0.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.intr_patt_done_ch0.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.intr_patt_done_ch0.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.intr_patt_done_ch0.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.intr_patt_done_ch0.d),
    .intr_o                 (intr_patt_done_ch0_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_intr_patt_done_ch1_o (
    .event_intr_i           (event_intr_patt_done_ch1),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.intr_patt_done_ch1.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.intr_patt_done_ch1.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.intr_patt_done_ch1.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.intr_patt_done_ch1.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.intr_patt_done_ch1.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.intr_patt_done_ch1.d),
    .intr_o                 (intr_patt_done_ch1_o)
  );
  
endmodule : pattgen_core
