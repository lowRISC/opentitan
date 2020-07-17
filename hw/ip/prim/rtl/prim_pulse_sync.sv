// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Pulse synchronizer: synchronizes a pulse from source clock domain (clk_src)
// to destination clock domain (clk_dst). Each pulse has the length of one clock
// cycle of its respective clock domain. Consecutive pulses need to be spaced
// appropriately apart from each other depending on the clock frequency ratio
// of the two clock domains.

module prim_pulse_sync (
  // source clock domain
  input  logic clk_src_i,
  input  logic rst_src_ni,
  input  logic src_pulse_i,
  // destination clock domain
  input  logic clk_dst_i,
  input  logic rst_dst_ni,
  output logic dst_pulse_o
);

  ////////////////////////////////////////////////////////////////////////////////
  // convert src_pulse to a level signal so we can use double-flop synchronizer //
  ////////////////////////////////////////////////////////////////////////////////
  logic src_level;

  always_ff @(posedge clk_src_i or negedge rst_src_ni) begin
    if (!rst_src_ni) begin
      src_level <= 1'b0;
    end else begin
      src_level <= src_level ^ src_pulse_i;
    end
  end

  //////////////////////////////////////////////////////////
  // synchronize level signal to destination clock domain //
  //////////////////////////////////////////////////////////
  logic dst_level;

  prim_flop_2sync #(.Width(1)) prim_flop_2sync (
    // source clock domain
    .d_i    (src_level),
    // destination clock domain
    .clk_i  (clk_dst_i),
    .rst_ni (rst_dst_ni),
    .q_o    (dst_level)
  );

  ////////////////////////////////////////
  // convert level signal back to pulse //
  ////////////////////////////////////////
  logic dst_level_q;

  // delay dst_level by 1 cycle
  always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
    if (!rst_dst_ni) begin
      dst_level_q <= 1'b0;
    end else begin
      dst_level_q <= dst_level;
    end
  end

  // edge detection
  assign dst_pulse_o = dst_level_q ^ dst_level;

endmodule
