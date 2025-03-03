// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pattgen_chan
  import pattgen_ctrl_pkg::*;
(
  input                       clk_i,
  input                       rst_ni,
  input  pattgen_chan_ctrl_t  ctrl_i,
  output logic                pda_o,
  output logic                pcl_o,
  output logic                event_done_o
);

  logic        enable;
  logic        polarity_q;
  logic        inactive_level_pcl_q;
  logic        inactive_level_pda_q;
  logic [31:0] prediv_q;
  logic [63:0] data_q;
  logic [5:0]  len_q;
  logic [9:0]  reps_q;

  logic        clk_en;
  logic        pcl_int_d;
  logic        pcl_int_q;
  logic [31:0] clk_cnt_d;
  logic [31:0] clk_cnt_q;
  logic        prediv_clk_rollover;

  logic        bit_cnt_en;
  logic [5:0]  bit_cnt_d;
  logic [5:0]  bit_cnt_q;

  logic        rep_cnt_en;
  logic [9:0]  rep_cnt_d;
  logic [9:0]  rep_cnt_q;

  logic        complete_en;
  logic        complete_d;
  logic        complete_q;
  logic        complete_q2;

  logic        active, active_d, active_q;

  // only accept new control signals when
  // enable is deasserted
  assign enable = ctrl_i.enable;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      polarity_q           <=  1'h0;
      inactive_level_pcl_q <=  1'h0;
      inactive_level_pda_q <=  1'h0;
      prediv_q             <= 32'h0;
      data_q               <= 64'h0;
      len_q                <=  6'h0;
      reps_q               <= 10'h0;
    end else begin
      polarity_q           <= enable ? polarity_q           : ctrl_i.polarity;
      inactive_level_pcl_q <= enable ? inactive_level_pcl_q : ctrl_i.inactive_level_pcl;
      inactive_level_pda_q <= enable ? inactive_level_pda_q : ctrl_i.inactive_level_pda;
      prediv_q             <= enable ? prediv_q             : ctrl_i.prediv;
      data_q               <= enable ? data_q               : ctrl_i.data;
      len_q                <= enable ? len_q                : ctrl_i.len;
      reps_q               <= enable ? reps_q               : ctrl_i.reps;
    end
  end

  // Drive pcl_o and pda_o directly from FF, so that they don't glitch.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pcl_o <= 1'b0;
      pda_o <= 1'b0;
    end else begin
      pcl_o <= active ? (polarity_q ? ~pcl_int_q : pcl_int_q)
                      : inactive_level_pcl_q;
      pda_o <= active ? data_q[bit_cnt_q]
                      : inactive_level_pda_q;
    end
  end

  // Hold the prediv counter and internal clock (PCL) once the previous pattern is complete
  assign clk_en = ~complete_q;

  // Predivision Counter -> Create an internal pulse (prediv_clk_rollover) which advances the
  // pattern generation state at the input clk frequency scaled down by the predivider.
  assign prediv_clk_rollover = (clk_cnt_q == prediv_q);
  assign clk_cnt_d = (!enable) ? 32'h0:
                     prediv_clk_rollover ? 32'h0 : // Rollover
                     (clk_cnt_q + 32'h1);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      clk_cnt_q <= 32'h0;
    end else begin
      clk_cnt_q <= clk_en ? clk_cnt_d : clk_cnt_q;
    end
  end

  // Generate an internal pattern clock (PCL)
  // - PCL toggles each time the predivider counter (clk_cnt_q) wraps.
  // - The internal PCL is zero at the start of the pattern and for the first period, only toggling
  //   at the end of the first period.
  // - The internal PCL is inverted at the output flop if configured to do so by the polarity.
  assign pcl_int_d = (!enable) ? 1'h0 :
                     prediv_clk_rollover ? ~pcl_int_q : // Rollover
                     pcl_int_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pcl_int_q <= 1'h0;
    end else begin
      pcl_int_q <= clk_en ? pcl_int_d : pcl_int_q;
    end
  end

  // Increment through bits of the pattern register, wrapping when the configured length is
  // reached. The index then muxes the current bit to the output with 'data_q[bit_cnt_q]'.
  // - Only update just before the falling edge of pcl_int
  // - Reset to zero immediately and do not increment when enable is inactive.
  assign bit_cnt_en = (pcl_int_q & prediv_clk_rollover) | (~enable);
  assign bit_cnt_d  = (!enable) ? 6'h0 :
                      (bit_cnt_q == len_q) ? 6'h0 : // Rollover
                      bit_cnt_q + 6'h1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cnt_q <= 6'h0;
    end else begin
      bit_cnt_q <= bit_cnt_en ? bit_cnt_d : bit_cnt_q;
    end
  end

  // Increment a counter for the number of times the pattern data is repeated within a single
  // activation. When the configured reps count is reached, the END state for this activation is
  // reached by signaling completion, and the counter resets.
  // - Increment as bit_cnt_q rolls over to zero.
  // - Reset to zero immediately and do not increment when enable is inactive.
  assign rep_cnt_en = (bit_cnt_en & (bit_cnt_q == len_q)) | (~enable);
  assign rep_cnt_d  = (!enable) ? 10'h0 :
                      (rep_cnt_q == reps_q) ? 10'h0 : // Rollover
                      rep_cnt_q + 10'h1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rep_cnt_q <= 10'h0;
    end else begin
      rep_cnt_q <= rep_cnt_en ? rep_cnt_d : rep_cnt_q;
    end
  end

  // Set the completion signal (complete_q) when rep_cnt reaches the configured limit and rolls
  // over to zero.
  // Clear / reset to zero when enable goes inactive.
  assign complete_en = (rep_cnt_en & (rep_cnt_q == reps_q)) | (~enable);
  assign complete_d  = (!enable) ? 1'h0 : 1'h1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      complete_q  <= 1'h0;
      complete_q2 <= 1'h0;
    end else begin
      complete_q  <= complete_en ? complete_d : complete_q;
      complete_q2 <= complete_q;
    end
  end

  // Trigger the event-type interrupt upon completion of the pattern.
  assign event_done_o = complete_q & ~complete_q2;

  // Track the state of the pattern generation with the 'active' signal (IDLE/END=0:ACTIVE=1)
  // _Transitions_
  // IDLE   -> (enable -> 1)     -> ACTIVE
  // ACTIVE -> (complete_q -> 1) -> END
  // ACTIVE -> (enable -> 0)     -> IDLE
  // END    -> (enable -> 0)     -> IDLE
  assign active_d = complete_q ? 1'b0 : // clearing on completion takes precedence
                    enable     ? 1'b1 : // set to active when enabled (and not complete)
                    active_q;           // otherwise hold
  assign active = enable ? active_d : active_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      active_q <= 1'b0;
    end else begin
      active_q <= active_d;
    end
  end

endmodule : pattgen_chan
