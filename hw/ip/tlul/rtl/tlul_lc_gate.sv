// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle gating module for TL-UL protocol.
// Transactions are passed through when lc_en_i == ON.
// In all other cases (lc_en_i != ON) incoming transactions return a bus error.
//
// Note that the lc_en_i should be synchronized and buffered outside of this module using
// an instance of prim_lc_sync.

module tlul_lc_gate
  import tlul_pkg::*;
  import lc_ctrl_pkg::*;
#(
  // Number of LC gating muxes in each direction.
  // It is recommended to set this parameter to 2, which results
  // in a total of 4 gating muxes.
  parameter int NumGatesPerDirection = 2
) (
  input clk_i,
  input rst_ni,

  // To host
  input  tl_h2d_t tl_h2d_i,
  output tl_d2h_t tl_d2h_o,

  // To device
  output tl_h2d_t tl_h2d_o,
  input  tl_d2h_t tl_d2h_i,

  // LC control signal
  input  lc_tx_t  lc_en_i
);

  //////////////////
  // Access Gates //
  //////////////////

  // Make a separate MUBI copy for each gating mux.
  lc_ctrl_pkg::lc_tx_t [2*NumGatesPerDirection:0] lc_en_buf;
  prim_lc_sync #(
    .NumCopies(2*NumGatesPerDirection+1),
    .AsyncOn(0)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_en_i),
    .lc_en_o(lc_en_buf)
  );

  tl_h2d_t tl_h2d_int [NumGatesPerDirection+1];
  tl_d2h_t tl_d2h_int [NumGatesPerDirection+1];
  for (genvar k = 0; k < NumGatesPerDirection; k++) begin : gen_lc_gating_muxes
    // H -> D path.
    tl_h2d_t tl_h2d_unbuf;
    assign tl_h2d_unbuf = (lc_tx_test_true_strict(lc_en_buf[2*k]))   ? tl_h2d_int[k]   : '0;
    // We do not want the tool to get smart about restructuring the muxes, hence we insert an
    // optimization barrier between them.
    prim_buf #(
      .Width($bits(tl_h2d_t))
    ) u_prim_buf_h2d (
      .in_i(tl_h2d_unbuf),
      .out_o(tl_h2d_int[k+1])
    );

    // D -> H path.
    tl_d2h_t tl_d2h_unbuf;
    assign tl_d2h_unbuf = (lc_tx_test_true_strict(lc_en_buf[2*k+1])) ? tl_d2h_int[k+1] : '0;
    // We do not want the tool to get smart about restructuring the muxes, hence we insert an
    // optimization barrier between them.
    prim_buf #(
      .Width($bits(tl_d2h_t))
    ) u_prim_buf_d2h (
      .in_i(tl_d2h_unbuf),
      .out_o(tl_d2h_int[k])
    );
  end

  // Assign signals on the device side.
  assign tl_h2d_o = tl_h2d_int[NumGatesPerDirection];
  assign tl_d2h_int[NumGatesPerDirection] = tl_d2h_i;

  ///////////////////////////
  // Host Side Interposing //
  ///////////////////////////

  // At the host side, we interpose the ready / valid signals so that we can return a bus error
  // in case the lc signal is not set to ON. Note that this logic does not have to be duplicated
  // since erroring back is considered a convenience feature so that the bus does not lock up.
  tl_h2d_t tl_h2d_error;
  tl_d2h_t tl_d2h_error;
  always_comb begin
    tl_h2d_int[0] = '0;
    tl_d2h_o      = '0;
    tl_h2d_error  = '0;

    if (lc_tx_test_true_strict(lc_en_buf[2*NumGatesPerDirection]) || !tl_d2h_error.d_valid) begin
      tl_h2d_int[0] = tl_h2d_i;
      tl_d2h_o      = tl_d2h_int[0];
    end else begin
      // In this case we route the incoming transactions through the error responder submodule.
      tl_h2d_error  = tl_h2d_i;
      tl_d2h_o      = tl_d2h_error;
    end
  end

  tlul_err_resp u_tlul_err_resp (
    .clk_i,
    .rst_ni,
    .tl_h_i(tl_h2d_error),
    .tl_h_o(tl_d2h_error)
  );

endmodule : tlul_lc_gate
