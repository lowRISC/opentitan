// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: pwm top module
//

module pwm_core #(
  parameter int unsigned MaxCnt = 40,
  parameter int unsigned MSB = 31
) (
  input logic        clk_i,
  input logic        rst_ni,
  // signals from/to control register block
  input              pwm_reg_pkg::pwm_reg2hw_t reg2hw,
  // PWM outputs
  output logic [8:0] pwm_o  // PWM outputs
);

  logic [MaxCnt-1:0] period_cntr_q, period_cntr_d;
  logic [8:0]        pwm_q, pwm_d;
  logic              rollover;
  logic [31:0]       period_cmp;

  // slide the compare window
  assign period_cmp = period_cntr_q[MSB:MSB-31];
  assign rollover = (period_cmp >= reg2hw.period.q);

  // Flopped here
  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      period_cntr_q <= {MaxCnt{1'b0}};
      pwm_q <= {9{1'b0}};
    end else begin
      period_cntr_q <= period_cntr_d;
      pwm_q <= pwm_d;
    end

  // create some shorter names
  logic cntr_en;
  assign cntr_en = reg2hw.cfg.cntr_en.q;
  logic [31:0] incr;
  assign incr = reg2hw.incr.q;
  logic [8:0] pwm_en;
  assign   pwm_en = reg2hw.cfg.pwm_en.q;

  // combinational for counter
  assign period_cntr_d = (!cntr_en || rollover) ? '0 :
                         cntr_en ? (period_cntr_q + {{MaxCnt-32{1'b0}}, incr}) :
                         period_cntr_q;

  // PWM signals
  // PWM = ON when counter is > posedge (via enables)
  // PWM = OFF when counter > negedge
  assign   pwm_d[0] = (period_cmp >= reg2hw.negedge_val_0.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_0.q) ? (cntr_en && pwm_en[0]) :
                      pwm_q[0];

  assign   pwm_d[1] = (period_cmp >= reg2hw.negedge_val_1.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_1.q) ? (cntr_en && pwm_en[1]) :
                      pwm_q[1];

  assign   pwm_d[2] = (period_cmp >= reg2hw.negedge_val_2.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_2.q) ? (cntr_en && pwm_en[2]) :
                      pwm_q[2];

  assign   pwm_d[3] = (period_cmp >= reg2hw.negedge_val_3.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_3.q) ? (cntr_en && pwm_en[3]) :
                      pwm_q[3];

  assign   pwm_d[4] = (period_cmp >= reg2hw.negedge_val_4.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_4.q) ? (cntr_en && pwm_en[4]) :
                      pwm_q[4];

  assign   pwm_d[5] = (period_cmp >= reg2hw.negedge_val_5.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_5.q) ? (cntr_en && pwm_en[5]) :
                      pwm_q[5];

  assign   pwm_d[6] = (period_cmp >= reg2hw.negedge_val_6.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_6.q) ? (cntr_en && pwm_en[6]) :
                      pwm_q[6];

  assign   pwm_d[7] = (period_cmp >= reg2hw.negedge_val_7.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_7.q) ? (cntr_en && pwm_en[7]) :
                      pwm_q[7];

  assign   pwm_d[8] = (period_cmp >= reg2hw.negedge_val_8.q) ? '0 :
                      (period_cmp >= reg2hw.posedge_val_8.q) ? (cntr_en && pwm_en[8]) :
                      pwm_q[8];

  assign pwm_o = pwm_q;

endmodule
