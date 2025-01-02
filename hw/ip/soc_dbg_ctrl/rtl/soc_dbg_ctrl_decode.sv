// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module soc_dbg_ctrl_decode #(
  parameter bit SyncDbgPolicy   = 1'b0,
  parameter bit SampleValidOnce = 1'b0
) (
  input  logic                              clk_i,
  input  logic                              rst_ni,
  input  soc_dbg_ctrl_pkg::soc_dbg_policy_t soc_dbg_policy_bus_i,
  // Decoded signals
  output logic                              relocked_o,
  output logic                              cat2_dbg_o,
  output logic                              cat3_dbg_o,
  output logic                              cat4_dbg_o
);

  ///////////////////////////////////////////////////////////////////////////////
  // Optional Synchronization + Sampling authentication state
  ///////////////////////////////////////////////////////////////////////////////

  prim_mubi_pkg::mubi4_t valid, relocked;

  if (SyncDbgPolicy) begin : gen_dbg_policy_sync
    prim_flop_2sync #(
      .Width      ( prim_mubi_pkg::MuBi4Width   ),
      .ResetValue ( {prim_mubi_pkg::MuBi4False} )
    ) u_sync_valid (
      .clk_i  ( clk_i                      ),
      .rst_ni ( rst_ni                     ),
      .d_i    ( soc_dbg_policy_bus_i.valid ),
      .q_o    ( valid                      )
    );

    prim_flop_2sync #(
      .Width      ( prim_mubi_pkg::MuBi4Width   ),
      .ResetValue ( {prim_mubi_pkg::MuBi4False} )
    ) u_sync_relocked (
      .clk_i  ( clk_i                         ),
      .rst_ni ( rst_ni                        ),
      .d_i    ( soc_dbg_policy_bus_i.relocked ),
      .q_o    ( relocked                      )
    );
  end else begin: gen_dbg_policy_async
    assign valid    = soc_dbg_policy_bus_i.valid;
    assign relocked = soc_dbg_policy_bus_i.relocked;
  end

  logic valid_decoded, relocked_decoded;
  assign valid_decoded    = prim_mubi_pkg::mubi4_test_true_strict(valid);
  assign relocked_decoded = prim_mubi_pkg::mubi4_test_false_strict(relocked);

  logic valid_rising;
  // Determine the rising edge of valid to latch the debug policy
  if (SampleValidOnce) begin : gen_sample_valid_once
    prim_edge_detector u_rising_valid (
      .clk_i             ( clk_i         ),
      .rst_ni            ( rst_ni        ),
      .d_i               ( valid_decoded ),
      .q_sync_o          (               ),
      .q_posedge_pulse_o ( valid_rising  ),
      .q_negedge_pulse_o (               )
    );
  end else begin : gen_sample_valid_every_cycle
    // Sample valid every cycle that valid is asserted when using a special CDC structure
    assign valid_rising = valid_decoded;
  end

  // Sample the debug policy on the rising edge of valid
  logic [$bits(soc_dbg_ctrl_pkg::dbg_category_e)-1:0] debug_category_logic_q;

  prim_flop_en #(
    .Width($bits(soc_dbg_ctrl_pkg::dbg_category_e)),
    .ResetValue({soc_dbg_ctrl_pkg::DbgCategoryLocked})
  ) u_sampled_policy (
    .clk_i  ( clk_i                         ),
    .rst_ni ( rst_ni                        ),
    .en_i   ( valid_rising                  ),
    .d_i    ( soc_dbg_policy_bus_i.category ),
    .q_o    ( debug_category_logic_q        )
  );

  soc_dbg_ctrl_pkg::dbg_category_e debug_category_q;
  assign debug_category_q = soc_dbg_ctrl_pkg::dbg_category_e'(debug_category_logic_q);

  // Output the decoded logic
  assign relocked_o = valid_decoded & relocked_decoded;
  assign cat4_dbg_o = debug_category_q == soc_dbg_ctrl_pkg::DbgCategory4;
  assign cat3_dbg_o = (cat4_dbg_o || debug_category_q == soc_dbg_ctrl_pkg::DbgCategory3) &&
                      !relocked_decoded;
  assign cat2_dbg_o = (cat4_dbg_o || cat3_dbg_o ||
                      debug_category_q == soc_dbg_ctrl_pkg::DbgCategory2) &&
                      !relocked_decoded;
endmodule
