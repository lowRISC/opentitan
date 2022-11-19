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
  parameter bit               EnablePrimCdcRand = 1
) (
  input                    clk_i,
  input                    rst_ni,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic [Width-1:0] d_o;
  logic [Width-1:0] intq;

`ifdef SIMULATION

  prim_cdc_rand_delay #(
    .DataWidth(Width),
    .Enable(EnablePrimCdcRand)
  ) u_prim_cdc_rand_delay (
    .clk_i,
    .rst_ni,
    .src_data_i(d_i),
    .prev_data_i(intq),
    .dst_data_o(d_o)
  );
`else // !`ifdef SIMULATION
  logic unused_sig;
  assign unused_sig = EnablePrimCdcRand;
  always_comb d_o = d_i;
`endif // !`ifdef SIMULATION

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
