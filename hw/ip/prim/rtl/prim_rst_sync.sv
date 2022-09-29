// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Reset synchronizer
/** Conventional 2FF async assert sync de-assert reset synchronizer
 *
 *
 * The sync module does not have scan input. Scan mux needs to be added after
 * this sync module.
 */

module prim_rst_sync #(
  // ActiveHigh should be 0 if the input reset is active low reset
  parameter bit ActiveHigh = 1'b 0,

  // CDC parameters
  parameter int CdcLatencyPs = 1000,
  parameter int CdcJitterPs  = 1000
) (
  input        clk_i,
  input        d_i, // raw reset (not synched to clk_i)
  output logic q_o  // reset synched to clk_i
);

  logic sync_rst_n;

  // TODO: Check if 2FF set can be used.
  if (ActiveHigh == 1'b 1) begin : g_rst_inv
    assign sync_rst_n = ~d_i;
  end else begin : g_rst_direct
    assign sync_rst_n = d_i;
  end

  prim_flop_2sync #(
    .Width        (1),
    .ResetValue   (ActiveHigh),
    .CdcLatencyPs (CdcLatencyPs),
    .CdcJitterPs  (CdcJitterPs)
  ) u_sync (
    .clk_i,
    .rst_ni (sync_rst_n ),
    .d_i    (!ActiveHigh), // reset release value
    .q_o
  );

endmodule : prim_rst_sync
