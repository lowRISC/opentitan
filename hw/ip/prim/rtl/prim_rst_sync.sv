// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Reset synchronizer
/** Conventional 2FF async assert sync de-assert reset synchronizer
 *
 */

module prim_rst_sync #(
  // ActiveHigh should be 0 if the input reset is active low reset
  parameter bit ActiveHigh = 1'b 0,

  // In certain case, Scan may be inserted at the following reset chain.
  // Set SkipScan to 1'b 1 in that case.
  parameter bit SkipScan   = 1'b 0
) (
  input        clk_i,
  input        d_i, // raw reset (not synched to clk_i)
  output logic q_o, // reset synched to clk_i

  // Scan chain
  input                        scan_rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i
);

  logic async_rst_n, scan_rst;
  logic rst_sync;

  // TODO: Check if 2FF set can be used.
  if (ActiveHigh == 1'b 1) begin : g_rst_inv
    assign async_rst_n = ~d_i;
    assign scan_rst    = ~scan_rst_ni;
  end else begin : g_rst_direct
    assign async_rst_n = d_i;
    assign scan_rst    = scan_rst_ni;
  end

  prim_flop_2sync #(
    .Width        (1),
    .ResetValue   (ActiveHigh)
  ) u_sync (
    .clk_i,
    .rst_ni (async_rst_n),
    .d_i    (!ActiveHigh), // reset release value
    .q_o    (rst_sync   )
  );

  if (SkipScan) begin : g_skip_scan
    logic  unused_scan;
    assign unused_scan = ^{scan_rst, scanmode_i};

    assign q_o = rst_sync;
  end else begin : g_scan_mux
    prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_scan_mux (
      .clk0_i(rst_sync                                         ),
      .clk1_i(scan_rst                                         ),
      .sel_i (prim_mubi_pkg::mubi4_test_true_strict(scanmode_i)),
      .clk_o (q_o                                              )
    );
  end

endmodule : prim_rst_sync
