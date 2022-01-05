// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Debounces the input signal and detects level changes.

module sysrst_ctrl_detect #(
  parameter int unsigned TimerWidth = 16,
  // If this parameter is set to 1, an edge is required for detection.
  // Otherwise the correct level (e.g. low for h2l) is sufficient.
  parameter bit EdgeDetect = 0,
  // If this parameter is set to 1, the l2h_detected_o and h2l_detected_o conditions can only be
  // reset by disabling the corresponding detector (cfg_l2h_en_i or cfg_h2l_en_i).
  parameter bit Sticky = 0
) (
  input                         clk_i,
  input                         rst_ni,
  input                         trigger_i,
  input        [TimerWidth-1:0] cfg_timer_i,
  input                         cfg_l2h_en_i,
  input                         cfg_h2l_en_i,
  output logic                  l2h_detected_o,
  output logic                  h2l_detected_o,
  output logic                  l2h_detected_pulse_o,
  output logic                  h2l_detected_pulse_o

);

  logic trigger_debounced_d;
  prim_filter_ctr #(
    .AsyncOn(0), // input signal has already been synced to the AON clock
    .CntWidth(TimerWidth)
  ) u_prim_filter_ctr (
    .clk_i,
    .rst_ni,
    .enable_i(1'b1),
    .filter_i(trigger_i),
    .thresh_i(cfg_timer_i),
    .filter_o(trigger_debounced_d)
  );

  logic h2l_event, l2h_event;
  if (EdgeDetect) begin : gen_edge_detect
    logic trigger_debounced_q;
    assign l2h_event = trigger_debounced_d & ~trigger_debounced_q;
    assign h2l_event = ~trigger_debounced_d & trigger_debounced_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg
      if (!rst_ni) begin
        trigger_debounced_q <= 1'b0;
      end else begin
        trigger_debounced_q <= trigger_debounced_d;
      end
    end
  end else begin : gen_level_only
    // In this case we just look at the signal level.
    assign l2h_event = trigger_debounced_d;
    assign h2l_event = ~trigger_debounced_d;
  end

  logic h2l_detected_d, h2l_detected_q;
  logic l2h_detected_d, l2h_detected_q;
  if (Sticky) begin : gen_sticky
    // Keep detected event until detector is disabled.
    assign l2h_detected_d = (cfg_l2h_en_i) ? (l2h_event | l2h_detected_q) : 1'b0;
    assign h2l_detected_d = (cfg_h2l_en_i) ? (h2l_event | h2l_detected_q) : 1'b0;
  end else begin : gen_not_sticky
    // Deassert automatically if the level does not remain stable after event.
    assign l2h_detected_d = (~trigger_debounced_d) ? 1'b0                         :
                            (cfg_l2h_en_i)         ? (l2h_event | l2h_detected_q) :
                                                     1'b0;
    assign h2l_detected_d = (trigger_debounced_d) ? 1'b0                         :
                            (cfg_h2l_en_i)        ? (h2l_event | h2l_detected_q) :
                                                    1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      l2h_detected_q <= 1'b0;
      h2l_detected_q <= 1'b0;
    end else begin
      l2h_detected_q <= l2h_detected_d;
      h2l_detected_q <= h2l_detected_d;
    end
  end

  assign l2h_detected_o = l2h_detected_d;
  assign h2l_detected_o = h2l_detected_d;
  assign l2h_detected_pulse_o = l2h_detected_d & ~l2h_detected_q;
  assign h2l_detected_pulse_o = h2l_detected_d & ~h2l_detected_q;

endmodule
