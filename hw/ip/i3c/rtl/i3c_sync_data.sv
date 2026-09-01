// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module is used to synchronize data...
// 1. from the intermittently-clocked SCL domain to the continuously-clocked IP domain.
//    Data loss shall be reported, but is not expected to occur because of the serial
//    nature of I3C, and the faster IP clock.
// 2. from the continuously-clocked IP domain to the intermittently-clocked SCL domain.
//    Data loss shall be prevented by the IP domain waiting on the 'src_toggle_o' change
//    before supplying new data and changing 'src_toggle_i' again.

module i3c_sync_data
#(
  parameter int unsigned Width = 1,
  parameter bit EnSrcToggleOut = 0
) (
  // Source clock domain.
  input               clk_src_i,
  input               rst_src_ni,
  input               src_toggle_i,
  output              src_toggle_o,
  input   [Width-1:0] src_data_i,
  // Destination clock domain.
  input               clk_dst_i,
  input               rst_dst_ni,
  output              dst_valid_o,
  input               dst_ready_i,
  output  [Width-1:0] dst_data_o
);

  // Transfer the source toggle signal into the destination domain.
  // - `src_toggle_i` switches between 0 and 1 whenever new data is to be presented to the
  //   destination domain.
  logic dst_toggle;
  prim_flop_2sync #(.Width(1)) u_sync_data(
    .clk_i  (clk_dst_i),
    .rst_ni (rst_dst_ni),
    .d_i    (src_toggle_i),
    .q_o    (dst_toggle)
  );

  // Anchor point for CDC exclusion; this data word effectively overtakes the toggle signal by
  // two destination clock cycles and changes infrequently relative to the destination clock,
  // so metastability is not an issue when capturing the data in the destination domain.
  logic [Width-1:0] dst_data;
  assign dst_data = src_data_i;

  logic dst_accepted;
  logic dst_new_data;
  logic dst_valid_q;
  logic dst_toggle_q;
  logic [Width-1:0] dst_data_q;

  assign dst_new_data = dst_toggle_q ^ dst_toggle;
  assign dst_accepted = dst_valid_q & dst_ready_i;
  assign dst_valid_o  = dst_valid_q;
  assign dst_data_o   = dst_data_q;

  always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
    if (!rst_dst_ni) begin
      dst_valid_q   <= 1'b0;
      dst_toggle_q  <= 1'b0;
      dst_data_q    <= '0;
    end else begin
      dst_valid_q   <= (dst_new_data | dst_valid_q) & ~dst_accepted;
      // Capture new data value 'immediately', bearing in mind that the destination clock may be
      // running intermittently (e.g. SCL).
      if (dst_new_data) dst_data_q <= dst_data;
      // Echo back the source toggle once the data is accepted.
      if (dst_accepted) dst_toggle_q <= dst_toggle;
    end
  end

  // Indication of data having been lost.
  assign dst_dataloss_o = dst_new_data & ~dst_accepted;

  // Echo the destination toggle back to the source domain if required.
  if (EnSrcToggleOut) begin : gen_src_toggle
    // Return toggle value to the source domain.
    prim_flop_2sync #(.Width(1)) u_sync_ack(
      .clk_i  (clk_src_i),
      .rst_ni (rst_src_ni),
      .d_i    (dst_toggle_q),
      .q_o    (src_toggle_o)
    );
  end else begin : gen_no_src_toggle
    assign src_toggle_o = src_toggle_i;
  end

endmodule
