// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM memory protection rule selection
// This module evaluates all defined protection regions against the incoming address.
// It identifies enabled regions that encompass the address and applies a priority-based selection
// where the lowest-indexed matching region takes precedence.

`include "prim_assert.sv"

module rram_ctrl_mp_region_sel import rram_ctrl_pkg::*; #(
  parameter int Regions = 4
) (
  input  logic             req_i,
  input  rram_phase_e      phase_i,
  input  logic [PageW-1:0] addr_i,
  input  mp_region_cfg_t   region_cfg_i[Regions],
  output page_cfg_t        page_cfg_o
);
  import prim_mubi_pkg::mubi4_test_true_strict;

  // Regions are allowed to overlap. Lower indices have priority
  logic [PageW:0]     region_end[Regions];
  logic [Regions-1:0] region_match;

  // Check for region match
  always_comb begin
    for (int i = 0; i < Regions; i++) begin : gen_region_comps
      region_end[i] = {1'b0, region_cfg_i[i].base} + region_cfg_i[i].size;

      // Region matches if address within range and if the partition matches
      region_match[i] = addr_i >= region_cfg_i[i].base &
                        {1'b0, addr_i} <= region_end[i] &
                        phase_i == region_cfg_i[i].phase &
                        mubi4_test_true_strict(region_cfg_i[i].cfg.en) &
                        req_i;
    end
  end

  // Select appropriate region configuration. Lowest region has the highest priority.
  always_comb begin
    page_cfg_o = CfgDisable;

    for (int i = Regions - 1; i >= 0; i--) begin: gen_region_cfg
      if (region_match[i]) begin
        page_cfg_o = region_cfg_i[i].cfg;
      end
    end
  end

endmodule // rram_ctrl_mp_region_sel
