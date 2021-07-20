// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pwm_chan (
  input        clk_i,
  input        rst_ni,

  input        pwm_en_i,
  input        invert_i,
  input        blink_en_i,
  input        htbt_en_i,
  input [15:0] phase_delay_i,
  input [15:0] duty_cycle_a_i,
  input [15:0] duty_cycle_b_i,
  input [15:0] blink_param_x_i,
  input [15:0] blink_param_y_i,

  input [15:0] phase_ctr_i,
  input        cycle_end_i,
  input        clr_blink_cntr_i,
  input [3:0]  dc_resn_i,

  output logic pwm_o
);

  logic [15:0] duty_cycle_actual;
  logic [15:0] on_phase;
  logic [15:0] off_phase;
  logic        phase_wrap;
  logic        pwm_int;

  // Standard blink mode
  logic [15:0] blink_ctr_q;
  logic [15:0] blink_ctr_d;
  logic [15:0] duty_cycle_blink;

  logic unused_sum;
  logic [15:0] blink_sum;
  assign {unused_sum, blink_sum} = blink_param_x_i + blink_param_y_i + 16'h1;
  assign blink_ctr_d = (!(blink_en_i && !htbt_en_i) || clr_blink_cntr_i) ? 16'h0 :
                       ((blink_ctr_q == blink_sum[15:0]) && cycle_end_i)
                       ? 16'h0 : (cycle_end_i) ? blink_ctr_q + 16'h1 : blink_ctr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      blink_ctr_q <= 16'h0;
    end else begin
      if (clr_blink_cntr_i) begin
        blink_ctr_q <= 16'h0;
      end else begin
        blink_ctr_q <= (blink_en_i && !htbt_en_i) ? blink_ctr_d : blink_ctr_q;
      end
    end
  end

  assign duty_cycle_blink = (blink_en_i && !htbt_en_i && (blink_ctr_q > blink_param_x_i)) ?
                            duty_cycle_b_i : duty_cycle_a_i;

  // Heartbeat mode
  logic [15:0] htbt_ctr_q;
  logic [15:0] htbt_ctr_d;
  logic [15:0] duty_cycle_htbt;
  logic [15:0] dc_htbt_d;
  logic [15:0] dc_htbt_q;
  logic dc_htbt_end;

  assign htbt_ctr_d = (!(blink_en_i && htbt_en_i) || clr_blink_cntr_i) ? 16'h0 :
                      ((htbt_ctr_q == blink_param_x_i) && cycle_end_i) ? 16'h0 :
                      (cycle_end_i) ? htbt_ctr_q + 16'h1 : htbt_ctr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      htbt_ctr_q <= 16'h0;
    end else begin
      if (clr_blink_cntr_i) begin
        htbt_ctr_q <= 16'h0;
      end else begin
        htbt_ctr_q <= (blink_en_i && htbt_en_i) ? htbt_ctr_d : htbt_ctr_q;
      end
    end
  end
  assign dc_htbt_end = cycle_end_i & (htbt_ctr_q == blink_param_x_i);

  logic htbt_direction;
  logic dc_wrap;
  logic pos_htbt;
  logic neg_htbt;
  assign pos_htbt = (duty_cycle_a_i < duty_cycle_b_i);
  assign neg_htbt = (duty_cycle_a_i > duty_cycle_b_i);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      htbt_direction <= '0;
    end else if (pos_htbt && ((dc_htbt_q >= duty_cycle_b_i) || (dc_wrap && dc_htbt_end))) begin
      htbt_direction <= 1'b1; // duty cycle counts down
    end else if (pos_htbt && (dc_htbt_q == duty_cycle_a_i) && dc_htbt_end) begin
      htbt_direction <= 1'b0; // duty cycle counts up
    end else if (neg_htbt && ((dc_htbt_q <= duty_cycle_b_i) || (dc_wrap && dc_htbt_end))) begin
      htbt_direction <= 1'b0; // duty cycle counts up
    end else if (neg_htbt && (dc_htbt_q == duty_cycle_a_i) && dc_htbt_end) begin
      htbt_direction <= 1'b1; // duty cycle counts down
    end else begin
      htbt_direction <= htbt_direction;
    end
  end

  logic pattern_repeat;
  assign pattern_repeat = (pos_htbt & htbt_direction) | (neg_htbt & ~htbt_direction) |
                          (~pos_htbt & ~neg_htbt);
  assign {dc_wrap, dc_htbt_d} = !(htbt_ctr_q == blink_param_x_i) ? {1'b0, dc_htbt_q} :
                                ((dc_htbt_q == duty_cycle_a_i) && pattern_repeat) ?
                                {1'b0, duty_cycle_a_i} : (htbt_direction) ?
                                {1'b0, dc_htbt_q} - {1'b0, blink_param_y_i} - 1'b1 :
                                {1'b0, dc_htbt_q} + {1'b0, blink_param_y_i} + 1'b1;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dc_htbt_q <= '0;
    end else if (!htbt_en_i && dc_htbt_q != duty_cycle_a_i) begin
      // the heart beat duty cycle is only changed when the heartbeat is not currently
      // ticking.
      dc_htbt_q <= duty_cycle_a_i;
    end else begin
      dc_htbt_q <= ((htbt_ctr_q == blink_param_x_i) && cycle_end_i) ? dc_htbt_d : dc_htbt_q;
    end
  end
  assign duty_cycle_htbt = dc_htbt_q;

  assign duty_cycle_actual = (blink_en_i && !htbt_en_i) ? duty_cycle_blink :
                             (blink_en_i && htbt_en_i) ? duty_cycle_htbt : duty_cycle_a_i;

  logic [30:0] phase_delay_scaled;
  logic [30:0] duty_cycle_scaled;
  logic [3:0] lshift;
  logic unused_shift;

  assign lshift = 4'd15 - dc_resn_i;
  assign phase_delay_scaled = phase_delay_i << lshift;
  assign duty_cycle_scaled = duty_cycle_actual << lshift;
  assign unused_shift = ^phase_delay_scaled | ^duty_cycle_scaled;

  assign on_phase = phase_delay_scaled[15:0];
  assign {phase_wrap, off_phase} = {1'b0, phase_delay_scaled[15:0]} +
                                   {1'b0, duty_cycle_scaled[15:0]};

  logic on_phase_exceeded;
  logic off_phase_exceeded;

  assign on_phase_exceeded  = (phase_ctr_i >= on_phase);
  assign off_phase_exceeded = (phase_ctr_i >= off_phase);

  assign pwm_int = !pwm_en_i ? 1'b0 :
                   phase_wrap ? on_phase_exceeded | ~off_phase_exceeded :
                                on_phase_exceeded & ~off_phase_exceeded;

  assign pwm_o = invert_i ? ~pwm_int : pwm_int;

endmodule : pwm_chan
