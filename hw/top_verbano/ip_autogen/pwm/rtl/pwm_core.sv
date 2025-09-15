// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: PWM Core Module

module pwm_core #(
  parameter int unsigned NOutputs = 6,
  parameter int unsigned PhaseCntDw = 16,
  parameter int unsigned BeatCntDw = 27
) (
  input                           clk_core_i,
  input                           rst_core_ni,

  input pwm_reg_pkg::pwm_reg2hw_t reg2hw,

  output logic [NOutputs-1:0]     pwm_o
);

  localparam int unsigned DcResnDw = $clog2(PhaseCntDw);

  // Reset internal counters whenever the phase counter becomes enabled; the new pulse cycle starts
  // immediately. The phase counter may be disabled at any time.
  logic                 cntr_en_q;
  logic [BeatCntDw-1:0] clk_div_q;
  logic [DcResnDw-1:0]  dc_resn_q;

  logic                clr_phase_cntr;
  logic [NOutputs-1:0] clr_chan_cntr;

  assign clr_phase_cntr = reg2hw.cfg.cntr_en.qe & reg2hw.cfg.cntr_en.q & ~cntr_en_q;

  // Capture channel state, in order to determine which channel(s) shall be reset when a shared
  // register is updated.
  logic [NOutputs-1:0] pwm_en_q;
  logic [NOutputs-1:0] invert_q;
  always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
    if (!rst_core_ni) begin
      pwm_en_q  <= '0;
      invert_q  <= '0;
    end else begin
      for (int unsigned ii = 0; ii < NOutputs; ii++) begin
        if (reg2hw.pwm_en[ii].qe) pwm_en_q[ii] <= reg2hw.pwm_en[ii].q;
      end
      for (int unsigned ii = 0; ii < NOutputs; ii++) begin
        if (reg2hw.invert[ii].qe) invert_q[ii] <= reg2hw.invert[ii].q;
      end
    end
  end

  for (genvar ii = 0; ii < NOutputs; ii++) begin : gen_chan_clr

    // Reset the internal timing state whenever any channel specific parameters change.
    //
    // Note that since many channels share a single 'pwm_en' and 'invert' register pair,
    // we perform this reset only when a channel becomes enabled (important for starting them
    // synchronized) or its inversion state is modified.

    assign clr_chan_cntr[ii] = (reg2hw.pwm_en[ii].qe & reg2hw.pwm_en[ii].q & ~pwm_en_q[ii]) |
                               (reg2hw.invert[ii].qe & (reg2hw.invert[ii].q ^ invert_q[ii])) |
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
  logic [DcResnDw-1:0]   dc_resn;
  logic [DcResnDw-1:0]   lshift;

  logic [BeatCntDw-1:0]  beat_ctr_q;
  logic [BeatCntDw-1:0]  beat_ctr_d;
  logic                  beat_end;

  logic [PhaseCntDw-1:0] phase_ctr_q;
  logic [PhaseCntDw-1:0] phase_ctr_d;
  logic [PhaseCntDw-1:0] phase_ctr_incr;
  logic [PhaseCntDw-1:0] phase_ctr_next;
  logic                  phase_ctr_overflow;
  logic                  phase_ctr_en;
  logic                  cycle_end;

  // Capture phase counter configuration when the counter becomes enabled.
  always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
    if (!rst_core_ni) begin
      cntr_en_q <= '0;
      clk_div_q <= '0;
      dc_resn_q <= '0;
    end else begin
      // Enabled state may be changed at any time.
      if (reg2hw.cfg.cntr_en.qe) cntr_en_q <= reg2hw.cfg.cntr_en.q;
      // Phase counter configuration is updated only when becoming enabled.
      if (clr_phase_cntr) begin
        clk_div_q <= reg2hw.cfg.clk_div.q;
        dc_resn_q <= reg2hw.cfg.dc_resn.q;
      end
    end
  end

  assign cntr_en = reg2hw.cfg.cntr_en.qe ? reg2hw.cfg.cntr_en.q : cntr_en_q;
  assign dc_resn = clr_phase_cntr        ? reg2hw.cfg.dc_resn.q : dc_resn_q;
  assign clk_div = clr_phase_cntr        ? reg2hw.cfg.clk_div.q : clk_div_q;

  // Write strobes are not used.
  logic unused_qe;
  assign unused_qe = ^{reg2hw.cfg.dc_resn.qe, reg2hw.cfg.clk_div.qe};

  assign beat_ctr_d = (clr_phase_cntr) ? '0 :
                      (beat_ctr_q == clk_div) ? '0 : (beat_ctr_q + 1'b1);
  assign beat_end = (beat_ctr_q == clk_div);

  always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
    if (!rst_core_ni) begin
      beat_ctr_q <= '0;
    end else if (cntr_en) begin
      beat_ctr_q <= beat_ctr_d;
    end
  end

  // Only update the phase counter ('phase_ctr_q') at the end of each beat.
  // Exception: allow reset to zero whenever the phase counter parameters are set.
  assign lshift = DcResnDw'(PhaseCntDw - 1'b1) - dc_resn;
  assign phase_ctr_en = clr_phase_cntr | (beat_end & cntr_en);
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
      .phase_ctr_next_i (phase_ctr_next),
      .cycle_end_i      (cycle_end),
      .clr_chan_cntr_i  (clr_chan_cntr[ii]),
      .dc_resn_i        (dc_resn),
      .pwm_o            (pwm_o[ii])
    );

  end : gen_chan_insts

  // unused register configuration
  logic unused_reg;
  assign unused_reg = ^reg2hw.alert_test;

endmodule : pwm_core
