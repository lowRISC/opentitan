// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pwm_chan #(
  parameter int CntDw = 16
) (
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
  logic [CntDw-1:0] blink_ctr_q;
  logic [CntDw-1:0] blink_ctr_d;
  logic [CntDw-1:0] duty_cycle_blink;

  logic unused_sum;
  logic [CntDw-1:0] blink_sum;
  assign {unused_sum, blink_sum} = blink_param_x_i + blink_param_y_i + 1'b1;
  assign blink_ctr_d = (!(blink_en_i && !htbt_en_i) || clr_blink_cntr_i) ? '0 :
                       ((blink_ctr_q == blink_sum[CntDw-1:0]) && cycle_end_i)
                       ? '0 : (cycle_end_i) ? blink_ctr_q + 1'b1 : blink_ctr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      blink_ctr_q <= '0;
    end else begin
      if (clr_blink_cntr_i) begin
        blink_ctr_q <= '0;
      end else begin
        blink_ctr_q <= (blink_en_i && !htbt_en_i) ? blink_ctr_d : blink_ctr_q;
      end
    end
  end

  assign duty_cycle_blink = (blink_en_i && !htbt_en_i && (blink_ctr_q > blink_param_x_i)) ?
                            duty_cycle_b_i : duty_cycle_a_i;

  // Heartbeat mode
  logic [CntDw-1:0] htbt_ctr_q;
  logic [CntDw-1:0] htbt_ctr_d;
  logic [CntDw-1:0] duty_cycle_htbt;
  logic [CntDw-1:0] dc_htbt_d;
  logic [CntDw-1:0] dc_htbt_q;
  logic dc_htbt_end;
  logic dc_htbt_end_q;

  assign htbt_ctr_d = (!(blink_en_i && htbt_en_i) || clr_blink_cntr_i) ? '0 :
                      ((htbt_ctr_q == blink_param_x_i) && cycle_end_i) ? '0 :
                      (cycle_end_i) ? (htbt_ctr_q + 1'b1) : htbt_ctr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      htbt_ctr_q <= '0;
    end else begin
      if (clr_blink_cntr_i) begin
        htbt_ctr_q <= '0;
      end else begin
        htbt_ctr_q <= (blink_en_i && htbt_en_i) ? htbt_ctr_d : htbt_ctr_q;
      end
    end
  end
  assign dc_htbt_end = cycle_end_i & (htbt_ctr_q == blink_param_x_i);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dc_htbt_end_q <= '0;
    end else begin
      dc_htbt_end_q <= dc_htbt_end;
    end
  end

  logic htbt_direction;
  logic dc_wrap;
  logic dc_wrap_q;
  logic pos_htbt;
  logic neg_htbt;
  assign pos_htbt = (duty_cycle_a_i < duty_cycle_b_i);
  assign neg_htbt = (duty_cycle_a_i > duty_cycle_b_i);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      htbt_direction <= '0;
    end else if (clr_blink_cntr_i) begin
      // For proper initialization, set the initial htbt_direction whenever a register is updated,
      // as indicated by clr_blink_cntr_i
      htbt_direction <= !pos_htbt;
    end else if (pos_htbt && ((dc_htbt_q >= duty_cycle_b_i) || (dc_wrap && dc_htbt_end))) begin
      htbt_direction <= 1'b1; // duty cycle counts down
    end else if (pos_htbt && (dc_htbt_q == duty_cycle_a_i) && dc_htbt_end_q) begin
      htbt_direction <= 1'b0; // duty cycle counts up
    end else if (neg_htbt && ((dc_htbt_q <= duty_cycle_b_i) || (dc_wrap && dc_htbt_end))) begin
      htbt_direction <= 1'b0; // duty cycle counts up
    end else if (neg_htbt && (dc_htbt_q == duty_cycle_a_i) && dc_htbt_end_q) begin
      htbt_direction <= 1'b1; // duty cycle counts down
    end else begin
      htbt_direction <= htbt_direction;
    end
  end

  logic pattern_repeat;
  assign pattern_repeat = (~pos_htbt & ~neg_htbt);
  localparam int CntExtDw = CntDw + 1;
  assign {dc_wrap, dc_htbt_d} = !(htbt_ctr_q == blink_param_x_i) ? (CntExtDw)'(dc_htbt_q) :
                                ((dc_htbt_q == duty_cycle_a_i) && pattern_repeat) ?
                                (CntExtDw)'(duty_cycle_a_i) : (htbt_direction) ?
                                (CntExtDw)'(dc_htbt_q) - (CntExtDw)'(blink_param_y_i) - 1'b1 :
                                (CntExtDw)'(dc_htbt_q) + (CntExtDw)'(blink_param_y_i) + 1'b1;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dc_wrap_q <= 1'b0;
    end else if ((htbt_ctr_q == blink_param_x_i) && cycle_end_i) begin
      // To pick the first dc_wrap pulse during the transition and set the correct duration of
      // dc_wrap_q, pos_htbt and htbt_direction signals are involved
      dc_wrap_q <= pos_htbt ? dc_wrap & ~htbt_direction : dc_wrap & htbt_direction;
    end else begin
      dc_wrap_q <= dc_wrap_q;
    end
  end
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

  assign duty_cycle_htbt = !dc_wrap_q ? dc_htbt_q : pos_htbt ? 16'hffff : '0;

  assign duty_cycle_actual = (blink_en_i && !htbt_en_i) ? duty_cycle_blink :
                             (blink_en_i && htbt_en_i) ? duty_cycle_htbt : duty_cycle_a_i;

  // For cases when the desired duty_cycle does not line up with the chosen resolution
  // we mask away any used bits.
  logic [15:0] dc_mask;
  // Mask is de-asserted for first dc_resn_i + 1 bits.
  // e.g. for dc_resn = 12, dc_mask = 16'b0000_0000_0000_0111
  // Bits marked as one in this mask are unused in computing
  // turn-on or turn-off times
  assign dc_mask = 16'hffff >> (dc_resn_i + 1);

  // Explicitly round down the phase_delay and duty_cycle
  logic [15:0] phase_delay_masked, duty_cycle_masked;
  assign phase_delay_masked = phase_delay_i & ~dc_mask;
  assign duty_cycle_masked  = duty_cycle_actual & ~dc_mask;

  assign on_phase                = phase_delay_masked;
  assign {phase_wrap, off_phase} = {1'b0, phase_delay_masked} +
                                   {1'b0, duty_cycle_masked};

  logic on_phase_exceeded;
  logic off_phase_exceeded;

  assign on_phase_exceeded  = (phase_ctr_i >= on_phase);
  assign off_phase_exceeded = (phase_ctr_i >= off_phase);

  assign pwm_int = !pwm_en_i ? 1'b0 :
                   phase_wrap ? on_phase_exceeded | ~off_phase_exceeded :
                                on_phase_exceeded & ~off_phase_exceeded;

  assign pwm_o = invert_i ? ~pwm_int : pwm_int;

endmodule : pwm_chan
