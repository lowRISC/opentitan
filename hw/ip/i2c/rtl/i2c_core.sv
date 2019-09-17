// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART core module

module  i2c_core (
  input                            clk_i,
  input                            rst_ni,

  input i2c_reg_pkg::i2c_reg2hw_t  reg2hw,
  output i2c_reg_pkg::i2c_hw2reg_t hw2reg,

  input                            scl_i,
  output logic                     scl_o,
  input                            sda_i,
  output logic                     sda_o,

  output logic                     intr_fmt_watermark_o,
  output logic                     intr_rx_watermark_o,
  output logic                     intr_fmt_overflow_o,
  output logic                     intr_rx_overflow_o,
  output logic                     intr_nak_o,
  output logic                     intr_scl_interference_o,
  output logic                     intr_sda_interference_o,
  output logic                     intr_stretch_timeout_o,
  output logic                     intr_sda_unstable_o
);

  logic [15:0] thigh;
  logic [15:0] tlow;
  logic [15:0] t_r;
  logic [15:0] t_f;
  logic [15:0] tsu_sta;
  logic [15:0] tsu_sto;
  logic [15:0] thd_st;
  logic [15:0] tsu_dat;
  logic [15:0] thd_dat;
  logic [15:0] t_buf;

  logic scl_out_fsm;
  logic sda_out_fsm;

  logic event_fmt_watermark;
  logic event_rx_watermark;
  logic event_fmt_overflow;
  logic event_rx_overflow;
  logic event_nak;
  logic event_scl_interference;
  logic event_sda_interference;
  logic event_stretch_timeout;
  logic event_sda_unstable;

  logic [15:0] scl_rx_val;
  logic [15:0] sda_rx_val;

  logic override;

  assign override = reg2hw.ovrd.txovrden;

  // placeholder until FSM in place
  assign sclout_fsm = 1'b0;
  assign sdaout_fsm = 1'b0;

  // placeholders for unused output registers
  assign hw2reg.status.fmtfull.d = 1'b0;
  assign hw2reg.status.rxfull.d = 1'b0;
  assign hw2reg.status.fmtempty.d = 1'b0;
  assign hw2reg.status.hostidle.d = 1'b1;
  assign hw2reg.status.targetidle.d = 1'b1;
  assign hw2reg.status.rxempty.d = 1'b0;
  assign hw2reg.fifo_status.fmtlvl.d = 5'b0;
  assign hw2reg.fifo_status.rxlvl.d = 5'b0;


  assign scl_o = override ? reg2hw.ovrd.sclval : scl_out_fsm;
  assign sda_o = override ? reg2hw.ovrd.sdaval : sda_out_fsm;

  // TODO: Establish a sample clock period for scl and sda
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
       scl_rx_val <= 16'h0;
       sda_rx_val <= 16'h0;
    end else begin
       scl_rx_val <= {scl_rx_val[14:0], scl_i};
       sda_rx_val <= {sda_rx_val[14:0], sda_i};
    end
  end

  assign hw2reg.val.scl_rx.d = scl_rx_val;
  assign hw2reg.val.sda_rx.d = sda_rx_val;

  assign thigh = reg2hw.timing0.thigh.q;
  assign tlow = reg2hw.timing0.tlow.q;
  assign t_r = reg2hw.timing1.t_r.q;
  assign t_f = reg2hw.timing1.t_f.q;
  assign tsu_sta = reg2hw.timing2.tsu_sta.q;
  assign thd_st = reg2hw.timing2.thd_st.q;
  assign tsu_dat = reg2hw.timing3.tsu_dat.q;
  assign thd_dat = reg2hw.timing3.thd_dat.q;
  assign tsu_sto = reg2hw.timing4.tsu_sto.q;
  assign t_buf = reg2hw.timing4.t_buf.q;

  assign event_fmt_watermark = 1'b0;
  assign event_rx_watermark = 1'b0;
  assign event_fmt_overflow = 1'b0;
  assign event_rx_overflow = 1'b0;
  assign event_nak = 1'b0;
  assign event_scl_interference = 1'b0;
  assign event_sda_interference = 1'b0;
  assign event_stretch_timeout = 1'b0;
  assign event_sda_unstable = 1'b0;

  prim_intr_hw #(.Width(1)) intr_hw_fmt_watermark (
    .event_intr_i           (event_fmt_watermark),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.fmt_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.fmt_watermark.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.fmt_watermark.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.fmt_watermark.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.fmt_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.fmt_watermark.d),
    .intr_o                 (intr_fmt_watermark_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_watermark (
    .event_intr_i           (event_rx_watermark),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_watermark.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_watermark.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_watermark.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_watermark.d),
    .intr_o                 (intr_rx_watermark_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_fmt_overflow (
    .event_intr_i           (event_fmt_overflow),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.fmt_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.fmt_overflow.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.fmt_overflow.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.fmt_overflow.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.fmt_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.fmt_overflow.d),
    .intr_o                 (intr_fmt_overflow_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_overflow (
    .event_intr_i           (event_rx_overflow),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_overflow.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_overflow.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_overflow.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_overflow.d),
    .intr_o                 (intr_rx_overflow_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_nak (
    .event_intr_i           (event_nak),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.nak.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.nak.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.nak.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.nak.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.nak.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.nak.d),
    .intr_o                 (intr_nak_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_scl_interference (
    .event_intr_i           (event_scl_interference),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.scl_interference.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.scl_interference.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.scl_interference.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.scl_interference.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.scl_interference.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.scl_interference.d),
    .intr_o                 (intr_scl_interference_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_sda_interference (
    .event_intr_i           (event_sda_interference),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.sda_interference.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.sda_interference.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.sda_interference.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.sda_interference.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.sda_interference.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.sda_interference.d),
    .intr_o                 (intr_sda_interference_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_stretch_timeout (
    .event_intr_i           (event_stretch_timeout),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.stretch_timeout.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.stretch_timeout.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.stretch_timeout.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.stretch_timeout.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.stretch_timeout.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.stretch_timeout.d),
    .intr_o                 (intr_stretch_timeout_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_sda_unstable (
    .event_intr_i           (event_sda_unstable),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.sda_unstable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.sda_unstable.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.sda_unstable.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.sda_unstable.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.sda_unstable.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.sda_unstable.d),
    .intr_o                 (intr_sda_unstable_o)
  );

endmodule
