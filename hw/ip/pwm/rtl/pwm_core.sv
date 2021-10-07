// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: PWM Core Module

module pwm_core #(
  parameter int NOutputs = 6,
  parameter int PhaseCntDw = 16,
  parameter int BeatCntDw = 27
) (
  input                           clk_core_i,
  input                           rst_core_ni,

  input pwm_reg_pkg::pwm_reg2hw_t reg2hw,

  output logic [NOutputs-1:0]     pwm_o
);

  // Reset internal counters whenever parameters change.

  logic                clr_phase_cntr;
  logic [NOutputs-1:0] clr_blink_cntr;

  assign clr_phase_cntr = reg2hw.cfg.clk_div.qe | reg2hw.cfg.dc_resn.qe | reg2hw.cfg.cntr_en.qe;

  for (genvar ii = 0; ii < NOutputs; ii++) begin : gen_chan_clr

    // Though it may be a bit overkill, we reset the internal blink counters whenever any channel
    // specific parameters change.

    assign clr_blink_cntr[ii] = reg2hw.pwm_en[ii].qe | reg2hw.invert[ii].qe |
                                reg2hw.pwm_param[ii].phase_delay.qe |
                                reg2hw.pwm_param[ii].htbt_en.qe |
                                reg2hw.pwm_param[ii].blink_en.qe |
                                reg2hw.duty_cycle[ii].a.qe |
                                reg2hw.duty_cycle[ii].b.qe |
                                reg2hw.blink_param[ii].x.qe |
                                reg2hw.blink_param[ii].y.qe;

  end : gen_chan_clr

  //
  // Beat and phase counters (in core clock domain)
  //

  logic                  cntr_en;
  logic [BeatCntDw-1:0]  clk_div;
  logic [3:0]            dc_resn;
  logic [3:0]            lshift;

  logic [BeatCntDw-1:0]  beat_ctr_q;
  logic [BeatCntDw-1:0]  beat_ctr_d;
  logic                  beat_ctr_en;
  logic                  beat_end;

  logic [PhaseCntDw-1:0] phase_ctr_q;
  logic [PhaseCntDw-1:0] phase_ctr_d;
  logic [PhaseCntDw-1:0] phase_ctr_incr;
  logic [PhaseCntDw-1:0] phase_ctr_next;
  logic                  phase_ctr_overflow;
  logic                  phase_ctr_en;
  logic                  cycle_end;

  assign cntr_en = reg2hw.cfg.cntr_en.q;
  assign dc_resn = reg2hw.cfg.dc_resn.q;
  assign clk_div = reg2hw.cfg.clk_div.q;

  assign beat_ctr_d = (clr_phase_cntr) ? '0 :
                      (beat_ctr_q == clk_div) ? '0 : (beat_ctr_q + 1'b1);
  assign beat_ctr_en = clr_phase_cntr | cntr_en;
  assign beat_end = (beat_ctr_q == clk_div);

  always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
    if (!rst_core_ni) begin
      beat_ctr_q <= '0;
    end else begin
      beat_ctr_q <= beat_ctr_en ? beat_ctr_d : beat_ctr_q;
    end
  end

  // Only update phase_ctr at the end of each beat
  // Exception: allow reset to zero whenever not enabled
  assign lshift = 4'd15 - dc_resn;
  assign phase_ctr_en = beat_end & (clr_phase_cntr | cntr_en);
  assign phase_ctr_incr =  (PhaseCntDw)'('h1) << lshift;
  assign {phase_ctr_overflow, phase_ctr_next} = phase_ctr_q + phase_ctr_incr;
  assign phase_ctr_d = clr_phase_cntr ? '0 : phase_ctr_next;
  assign cycle_end = beat_end & phase_ctr_overflow;

  always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
    if (!rst_core_ni) begin
      phase_ctr_q <= '0;
    end else begin
      phase_ctr_q <= phase_ctr_en ? phase_ctr_d : phase_ctr_q;
    end
  end

  for (genvar ii = 0; ii < NOutputs; ii++) begin : gen_chan_insts

    //
    // PWM Channel Instantiation
    //

    pwm_chan #(.CntDw(PhaseCntDw)) u_chan (
      .clk_i            (clk_core_i),
      .rst_ni           (rst_core_ni),
      .pwm_en_i         (reg2hw.pwm_en[ii].q),
      .invert_i         (reg2hw.invert[ii].q),
      .phase_delay_i    (reg2hw.pwm_param[ii].phase_delay.q),
      .blink_en_i       (reg2hw.pwm_param[ii].blink_en.q),
      .htbt_en_i        (reg2hw.pwm_param[ii].htbt_en.q),
      .duty_cycle_a_i   (reg2hw.duty_cycle[ii].a.q),
      .duty_cycle_b_i   (reg2hw.duty_cycle[ii].b.q),
      .blink_param_x_i  (reg2hw.blink_param[ii].x.q),
      .blink_param_y_i  (reg2hw.blink_param[ii].y.q),
      .phase_ctr_i      (phase_ctr_q),
      .clr_blink_cntr_i (clr_blink_cntr[ii]),
      .cycle_end_i      (cycle_end),
      .dc_resn_i        (dc_resn),
      .pwm_o            (pwm_o[ii])
    );

  end : gen_chan_insts

  // unused register configuration
  logic unused_reg;
  assign unused_reg = ^reg2hw.alert_test;

endmodule : pwm_core
