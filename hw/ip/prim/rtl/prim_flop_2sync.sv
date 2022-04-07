// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic double-synchronizer flop
// This may need to be moved to prim_generic if libraries have a specific cell
// for synchronization

module prim_flop_2sync #(
  parameter int               Width      = 16,
  parameter logic [Width-1:0] ResetValue = '0,
  parameter int               CdcLatencyPs = 1000,
  parameter int               CdcJitterPs = 1000
) (
  input                    clk_i,
  input                    rst_ni,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic [Width-1:0] d_o;

  prim_cdc_rand_delay #(
    .DataWidth(Width),
    .UseSourceClock(0),
    .LatencyPs(CdcLatencyPs),
    .JitterPs(CdcJitterPs)
  ) u_prim_cdc_rand_delay (
    .src_clk(),
    .src_data(d_i),
    .dst_clk(clk_i),
    .dst_data(d_o)
  );

  logic [Width-1:0] intq;

  prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_sync_1 (
    .clk_i,
    .rst_ni,
    .d_i(d_o),
    .q_o(intq)
  );

  prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_sync_2 (
    .clk_i,
    .rst_ni,
    .d_i(intq),
    .q_o
  );

endmodule : prim_flop_2sync
