// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Memory Properties
//

`include "prim_assert.sv"

module flash_mp_data_region_sel import flash_ctrl_pkg::*; #(
  parameter int Regions = 4
) (
  input req_i,
  input flash_lcmgr_phase_e phase_i,
  input [AllPagesW-1:0] addr_i,
  input data_region_attr_t region_attrs_i [Regions],
  output mp_region_cfg_t sel_cfg_o
);
  import prim_mubi_pkg::mubi4_test_true_strict;

  // There could be multiple region matches due to region overlap
  // Lower indices always have priority
  logic [AllPagesW:0] region_end[Regions];
  logic [Regions-1:0] region_match;
  logic [Regions-1:0] region_sel;

  // decode for software interface region
  assign region_sel[0] = region_match[0];
  for (genvar i = 1; i < Regions; i++) begin: gen_region_priority
    assign region_sel[i] = region_match[i] & ~|region_match[i-1:0];
  end

  // check for region match
  always_comb begin
    for (int i = 0; i < Regions; i++) begin: gen_region_comps
      region_end[i] = {1'b0, region_attrs_i[i].cfg.base} + region_attrs_i[i].cfg.size;

      // region matches if address within range and if the partition matches
      region_match[i] = addr_i >= region_attrs_i[i].cfg.base &
                        {1'b0, addr_i} < region_end[i] &
                        phase_i == region_attrs_i[i].phase &
                        mubi4_test_true_strict(region_attrs_i[i].cfg.en) &
                        req_i;
    end
  end

  // select appropriate region configuration
  always_comb begin
    sel_cfg_o = '0;
    for (int i = 0; i < Regions; i++) begin: gen_region_sel
      if (region_sel[i]) begin
        sel_cfg_o = region_attrs_i[i].cfg;
      end
    end
  end


endmodule // flash_mp_data_region_sel
