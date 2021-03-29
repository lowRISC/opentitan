// Copyright lowRISC contributors.
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
  logic [31:0] prediv_q;
  logic [63:0] data_q;
  logic [5:0]  len_q;
  logic [9:0]  reps_q;

  logic        clk_en;
  logic        pcl_int_d;
  logic        pcl_int_q;
  logic [31:0] clk_cnt_d;
  logic [31:0] clk_cnt_q;

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

  // only accept new control signals when
  // enable is deasserted
  assign enable = ctrl_i.enable;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      polarity_q <=  1'h0;
      prediv_q   <= 32'h0;
      data_q     <= 64'h0;
      len_q      <=  6'h0;
      reps_q     <= 10'h0;
    end else begin
      polarity_q <= enable ? polarity_q : ctrl_i.polarity;
      prediv_q   <= enable ? prediv_q   : ctrl_i.prediv;
      data_q     <= enable ? data_q     : ctrl_i.data;
      len_q      <= enable ? len_q      : ctrl_i.len;
      reps_q     <= enable ? reps_q     : ctrl_i.reps;
    end
  end

  assign pcl_int_d = (!enable) ? 1'h0 :
                     (clk_cnt_q == prediv_q) ? ~pcl_int_q : pcl_int_q;
  assign clk_cnt_d = (!enable) ? 32'h0:
                     (clk_cnt_q == prediv_q) ? 32'h0 : (clk_cnt_q + 32'h1);
  assign pcl_o     = polarity_q ? ~pcl_int_q : pcl_int_q;

  // disable the clock if the previous pattern is complete
  assign clk_en    = ~complete_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pcl_int_q <= 1'h0;
      clk_cnt_q <= 32'h0;
    end else begin
      pcl_int_q <= clk_en ? pcl_int_d : pcl_int_q;
      clk_cnt_q <= clk_en ? clk_cnt_d : clk_cnt_q;
    end
  end

  // Only update just before the falling edge of pcl_int
  // Exception: allow reset to zero whenever not enabled
  assign bit_cnt_en = (pcl_int_q & (clk_cnt_q == prediv_q) ) | (~enable);
  assign bit_cnt_d  = (!enable) ? 6'h0:
                      (bit_cnt_q == len_q) ? 6'h0 : bit_cnt_q + 6'h1;
  assign pda_o      = (!enable) ? 1'b0 : data_q[bit_cnt_q];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cnt_q <= 6'h0;
    end else begin
      bit_cnt_q <= bit_cnt_en ? bit_cnt_d : bit_cnt_q;
    end
  end

  // Only update just bit_cnt_q rolls over to zero.
  // Exception: allow reset to zero whenever not enabled
  assign rep_cnt_en = (bit_cnt_en & (bit_cnt_q == len_q)) | (~enable);
  assign rep_cnt_d  = (!enable) ? 10'h0 :
                      (rep_cnt_q == reps_q) ? 10'h0 : rep_cnt_q + 10'h1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rep_cnt_q <= 10'h0;
    end else begin
      rep_cnt_q <= rep_cnt_en ? rep_cnt_d : rep_cnt_q;
    end
  end

  // flip the complete bit to 1 whenever the rep_cnt is about to roll over to zero.
  // Also clear to zero whenever not enabled.
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

  assign event_done_o = complete_q & ~complete_q2;

endmodule : pattgen_chan
