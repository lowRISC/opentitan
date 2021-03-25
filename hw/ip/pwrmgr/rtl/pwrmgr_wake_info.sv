// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Wake Information
//

`include "prim_assert.sv"

module pwrmgr_wake_info import pwrmgr_pkg::*; import pwrmgr_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  input wr_i,
  input [TotalWakeWidth-1:0] data_i,
  input start_capture_i,
  input record_dis_i,
  input [NumWkups-1:0] wakeups_i,
  input fall_through_i,
  input abort_i,
  output pwrmgr_hw2reg_wake_info_reg_t info_o
);

  logic record_en;

  // detect rising edge of start_capture_i
  logic start_capture_q1, start_capture;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_capture_q1 <= 1'b1;
    end else begin
      start_capture_q1 <= start_capture_i;
    end
  end

  assign start_capture = start_capture_i & ~start_capture_q1;

  // generate the record enbale signal
  // HW enables the recording
  // Software can suppress the recording or disable it
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      record_en <= 1'b0;
    end else if (start_capture && !record_dis_i) begin
      // if not disabled by software
      // a recording enable puls by HW starts recording
      record_en <= 1'b1;
    end else if (record_dis_i && record_en) begin
      // if recording is already ongoing
      // a disable command by software shuts things down
      record_en <= 1'b0;
    end
  end

  logic [TotalWakeWidth-1:0] info;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      info <= '0;
    end else if (wr_i) begin
      info <= info & ~data_i; // W1C
    end else if (record_en) begin // If set once, hold until clear
      info[0 +: NumWkups] <= info[0 +: NumWkups] | wakeups_i;
      info[NumWkups +: 2] <= info[NumWkups +: 2] | {abort_i, fall_through_i};
    end
  end

  // assign outputs
  assign info_o.abort.d = info[NumWkups + 1];
  assign info_o.fall_through.d = info[NumWkups];
  assign info_o.reasons = info[NumWkups-1:0];



endmodule
