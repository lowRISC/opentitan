// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Pulse synchronizer with data latching
// This module also returns a pulse to indicate the latching has completed

module prim_pulse_sync_data #(
  parameter int DataWidth = 1,
  parameter logic [DataWidth-1:0] ResetValue = '0
) (
  // source clock domain
  input  logic clk_src_i,
  input  logic rst_src_ni,
  input  logic src_pulse_i,
  input  logic [DataWidth-1:0] src_data_i,
  output logic src_ack_pulse_o,
  // destination clock domain
  input  logic clk_dst_i,
  input  logic rst_dst_ni,
  output logic dst_pulse_o,
  output logic [DataWidth-1:0] dst_data_o
);

  logic dst_pulse;

  prim_pulse_sync u_ctrl_sync (
    .clk_src_i,
    .rst_src_ni,
    .src_pulse_i,
    .clk_dst_i,
    .rst_dst_ni,
    .dst_pulse_o(dst_pulse)
  );

  always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
    if (!rst_dst_ni) begin
      dst_data_o <= ResetValue;
    end else if (dst_pulse) begin
      dst_data_o <= src_data_i;
    end
  end

  always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
    if (!rst_dst_ni) begin
      dst_pulse_o <= '0;
    end else begin
      dst_pulse_o <= dst_pulse;
    end
  end

  // sync destination pulse back to source domain for acknowledge
  prim_pulse_sync u_ctrl_ack_sync (
    .clk_src_i(clk_dst_i),
    .rst_src_ni(rst_dst_ni),
    .src_pulse_i(dst_pulse),
    .clk_dst_i(clk_src_i),
    .rst_dst_ni(rst_src_ni),
    .dst_pulse_o(src_ack_pulse_o)
  );


endmodule
