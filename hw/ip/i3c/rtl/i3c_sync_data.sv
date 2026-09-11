// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is used to synchronize data..
// 1. ..from the intermittently-clocked SCL domain to the continuously-clocked IP domain.
//    Data loss shall be reported, but is not expected to occur because of the serial
//    nature of I3C, and the faster IP clock,
// 2. ..from the continuously-clocked IP domain to the intermittently-clocked SCL domain.
//    Data loss shall be prevented by the IP domain waiting on the 'src_toggle_o' change
//    before supplying new data and changing 'src_toggle_i' again.

`include "prim_assert.sv"

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
  output  [Width-1:0] dst_data_o,
  output              dst_dataloss_o
);

  // Transfer the source toggle signal into the destination domain.
  // - `src_toggle_i` switches between 0 and 1 whenever new data is to be presented to the
  //   destination domain.
  logic dst_toggle;
  prim_flop_2sync #(.Width(1)) u_sync_tgl_req (
    .clk_i (clk_dst_i),
    .rst_ni(rst_dst_ni),
    .d_i   (src_toggle_i),
    .q_o   (dst_toggle)
  );

  logic             dst_capture;
  logic             dst_accepted;
  logic             dst_valid_q;
  logic             dst_toggle_q;
  logic             dst_toggle_raw_q;
  logic             dst_toggle_edge;
  logic [Width-1:0] dst_data;
  logic [Width-1:0] dst_data_q;

  // Anchor point for CDC exclusion; this data word effectively overtakes the toggle signal by
  // two destination clock cycles and changes infrequently relative to the destination clock,
  // so metastability is not an issue when capturing the data in the destination domain.
  assign dst_data = src_data_i;

  assign dst_toggle_edge = dst_toggle_raw_q ^ dst_toggle;
  assign dst_capture     = dst_toggle_edge & (~dst_valid_q | dst_ready_i);
  assign dst_accepted    = dst_valid_q & dst_ready_i;
  assign dst_valid_o     = dst_valid_q;
  assign dst_data_o      = dst_data_q;

  always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
    if (!rst_dst_ni) begin
      dst_valid_q      <= 1'b0;
      dst_toggle_q     <= 1'b0;
      dst_toggle_raw_q <= 1'b0;
      dst_data_q       <= '0;
    end else begin
      // Simply delay the toggle signal by one cycle
      dst_toggle_raw_q <= dst_toggle;
      // Only clear a set flag if there is no new edge and we saw an accept condition
      dst_valid_q <= dst_toggle_edge | (dst_valid_q & ~dst_accepted);
      // Capture new data value 'immediately', bearing in mind that the destination clock may be
      // running intermittently (e.g., SCL).
      if (dst_capture) dst_data_q <= dst_data;
      // Flip toggle value once the data is accepted.
      if (dst_accepted) dst_toggle_q <= ~dst_toggle_q;
    end
  end

  // Indication of data having been lost.
  assign dst_dataloss_o = dst_toggle_edge & dst_valid_q & !dst_ready_i;

  // Echo the destination toggle back to the source domain if required.
  if (EnSrcToggleOut) begin : gen_src_toggle
    // Return toggle value to the source domain.
    prim_flop_2sync #(.Width(1)) u_sync_tgl_ack (
      .clk_i  (clk_src_i),
      .rst_ni (rst_src_ni),
      .d_i    (dst_toggle_q),
      .q_o    (src_toggle_o)
    );

    // The source domain must hold src_toggle_i (and hence src_data_i) stable while a transfer is
    // outstanding, i.e., until src_toggle_o echoes the value back. Pushing a second data word while
    // the first toggle feedback is still outstanding can lead to data loss.
    `ASSERT(SrcToggleStableWhileOutstandingA,
        $past(src_toggle_i) != $past(src_toggle_o) |-> $stable(src_toggle_i),
        clk_src_i, !rst_src_ni)
  end else begin : gen_no_src_toggle
    assign src_toggle_o = 1'b0;
  end

  // src_data_i crosses combinationally, so by the time a toggle transition is observed here, the
  // data must have already been stable for the full synchronizer depth.
  `ASSERT(SrcDataStableAroundToggleEdgeA,
    dst_toggle_edge |-> $stable(src_data_i) && $past($stable(src_data_i)),
    clk_dst_i, !rst_dst_ni)

endmodule
