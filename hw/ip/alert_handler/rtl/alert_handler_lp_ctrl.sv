// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module gathers and synchronizes the clock gating and reset indication signals for all
// low-power groups (LPGs), synchronizes them to the alert handler clock domain.
// The clock gating and reset indication signals are then logically OR'ed to produce one multibit
// value for each LPG. The LPG multibit values are then mapped to the alert channels using
// the AlertLpgMap parameter, and each multibit output value is buffered independently.
//

`include "prim_assert.sv"

module alert_handler_lp_ctrl import alert_pkg::*; (
  input  clk_i,
  input  rst_ni,
  // Low power clk and rst indication signals.
  input  lc_ctrl_pkg::lc_tx_t [NLpg-1:0]    lpg_cg_en_i,
  input  lc_ctrl_pkg::lc_tx_t [NLpg-1:0]    lpg_rst_en_i,
  // Init requests going to the individual alert channels.
  output lc_ctrl_pkg::lc_tx_t [NAlerts-1:0] init_trig_o
);

  ///////////////////////////////////////////////////
  // Aggregate multibit indication signals per LPG //
  ///////////////////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t [NLpg-1:0] lpg_init_trig;
  for (genvar k = 0; k < NLpg; k++) begin : gen_lpgs

    lc_ctrl_pkg::lc_tx_t [0:0] lpg_cg_en;
    prim_lc_sync u_prim_lc_sync_clk_en (
      .clk_i,
      .rst_ni,
      .lc_en_i(lpg_cg_en_i[k]),
      .lc_en_o(lpg_cg_en)
    );
    lc_ctrl_pkg::lc_tx_t [0:0] lpg_rst_en;
    prim_lc_sync u_prim_lc_sync_rst_en (
      .clk_i,
      .rst_ni,
      .lc_en_i(lpg_rst_en_i[k]),
      .lc_en_o(lpg_rst_en)
    );

    // Perform a logical OR operation of the multibit life cycle signals.
    // I.e., if any of the incoming multibit signals is On, the output will also be On.
    // Otherwise, the output may have any value other than On.
    prim_lc_combine #(
      .ActiveLow(0),  // Active Value is "On"
      .CombineMode(0) // Combo mode is "OR"
    ) u_prim_lc_combine (
      .lc_en_a_i(lpg_cg_en[0]),
      .lc_en_b_i(lpg_rst_en[0]),
      .lc_en_o  (lpg_init_trig[k])
    );
  end

  //////////////////////////////////
  // LPG to Alert Channel Mapping //
  //////////////////////////////////

  // select the correct lpg for the alert channel at index j and buffer the multibit signal for each
  // alert channel.
  for (genvar j=0; j < NAlerts; j++) begin : gen_alert_map
    prim_lc_sync #(
      .AsyncOn(0) // no sync flops
    ) u_prim_lc_sync_lpg_en (
      .clk_i,
      .rst_ni,
      .lc_en_i(lpg_init_trig[AlertLpgMap[j]]),
      .lc_en_o({init_trig_o[j]})
    );
  end

endmodule : alert_handler_lp_ctrl
