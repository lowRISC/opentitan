// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module gathers and synchronizes the clock gating and reset indication signals for all
// low-power groups (LPGs), synchronizes them to the alert handler clock domain. The clock gating
// and reset indication signals are then logically OR'ed to produce one multibit value for each
// LPG. The LPG multibit values are then mapped to the alert channels using the LpgMap parameter,
// and each multibit output value is buffered independently.
//

`include "prim_assert.sv"

module alert_handler_lpg_ctrl import alert_pkg::*; (
  input  clk_i,
  input  rst_ni,
  // Low power clk and rst indication signals.
  input  prim_mubi_pkg::mubi4_t [NLpg-1:0]    lpg_cg_en_i,
  input  prim_mubi_pkg::mubi4_t [NLpg-1:0]    lpg_rst_en_i,
  // Init requests going to the individual alert channels.
  output prim_mubi_pkg::mubi4_t [NAlerts-1:0] alert_init_trig_o
);

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_or_hi;
  import prim_mubi_pkg::MuBi4True;

  ///////////////////////////////////////////////////
  // Aggregate multibit indication signals per LPG //
  ///////////////////////////////////////////////////

  mubi4_t [NLpg-1:0] synced_lpg_cg_en, synced_lpg_rst_en, lpg_init_trig;
  for (genvar k = 0; k < NLpg; k++) begin : gen_lpgs
    prim_mubi4_sync #(
      .ResetValue(MuBi4True)
    ) u_prim_mubi4_sync_cg_en (
      .clk_i,
      .rst_ni,
      .mubi_i(lpg_cg_en_i[k]),
      .mubi_o(synced_lpg_cg_en[k:k])
    );
    prim_mubi4_sync #(
      .ResetValue(MuBi4True)
    ) u_prim_mubi4_sync_rst_en (
      .clk_i,
      .rst_ni,
      .mubi_i(lpg_rst_en_i[k]),
      .mubi_o(synced_lpg_rst_en[k:k])
    );

    // Perform a logical OR operation of the multibit life cycle signals.
    // I.e., if any of the incoming multibit signals is On, the output will also be On.
    // Otherwise, the output may have any value other than On.
    assign lpg_init_trig[k] = mubi4_or_hi(synced_lpg_cg_en[k], synced_lpg_rst_en[k]);
  end

  //////////////////////////////////
  // LPG to Alert Channel Mapping //
  //////////////////////////////////

  // select the correct lpg for the alert channel at index j and buffer the multibit signal for each
  // alert channel.
  for (genvar j=0; j < NAlerts; j++) begin : gen_alert_map
    prim_mubi4_sync #(
      .AsyncOn(0) // no sync flops
    ) u_prim_mubi4_sync_lpg_en (
      .clk_i,
      .rst_ni,
      .mubi_i(lpg_init_trig[LpgMap[j]]),
      .mubi_o({alert_init_trig_o[j]})
    );
  end

  // explicitly read all unused lpg triggers to avoid lint errors.
  logic [NLpg-1:0] lpg_used;
  logic unused_lpg_init_trig;
  always_comb begin
    lpg_used = '0;
    unused_lpg_init_trig = 1'b0;
    for (int j=0; j < NAlerts; j++) begin
      lpg_used[LpgMap[j]] |= 1'b1;
    end
    for (int k=0; k < NLpg; k++) begin
      if (!lpg_used) begin
        unused_lpg_init_trig ^= ^lpg_init_trig[k];
      end
    end
  end

endmodule : alert_handler_lpg_ctrl
