// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Simple address translation for rv_core_ibex
 * This performs a configurable address translation, please see
 * https://docs.google.com/document/d/1uU2Zh46SJtoaOqZ9dCRO7oAQnhTUcWWZ7CstOa1PZiM/edit?usp=sharing
 */

module rv_core_addr_trans import rv_core_ibex_pkg::*; #(
  parameter int AddrWidth = 32,
  parameter int NumRegions = 2
) (
  input logic clk_i,
  input logic rst_ni,
  input region_cfg_t [NumRegions-1:0] region_cfg_i,
  input logic [AddrWidth-1:0] addr_i,
  output logic [AddrWidth-1:0] addr_o
);

  typedef struct packed {
    logic [AddrWidth-1:0] output_mask;
    logic [AddrWidth-1:0] remap_addr;
  } region_ctrls_t;

  region_ctrls_t region_ctrls [NumRegions] ;
  logic [NumRegions-1:0][AddrWidth-1:0] input_masks;

  // Mask generation is based on the matching region configuration
  // Since matching is done on a power-of-2 alignment, the mechanism is similar
  // to RISC-V pmp's power-of-2 usage.
  // As an example:
  // If a matching region is programmed as 0x8007_FFFF,
  // The matching input mask is 0xFFF0_0000
  // The output mask is simply inverted 0x000F_FFFF
  for (genvar i = 0; i < NumRegions; i++) begin : gen_region_ctrls
    assign input_masks[i][0] = 1'b0;

    for (genvar j = 1; j < AddrWidth; j++) begin : gen_addr_masks_lower_bits
      assign input_masks[i][j] = ~&region_cfg_i[i].matching_region[j-1:0];
    end

    // pack things into region controls
    assign region_ctrls[i].output_mask = ~input_masks[i];
    assign region_ctrls[i].remap_addr = region_cfg_i[i].remap_addr;
  end

  logic [NumRegions-1:0] all_matches;
  for (genvar i = 0; i < NumRegions; i++) begin : gen_region_matches
    assign all_matches[i] = region_cfg_i[i].en &
                            ((region_cfg_i[i].matching_region & input_masks[i]) ==
                            (addr_i & input_masks[i]));
  end

  logic sel_match;
  region_ctrls_t sel_region;
  prim_arbiter_fixed #(
    .N(NumRegions),
    .DW($bits(region_ctrls_t)),
    .EnDataPort(1)
  ) u_sel_region (
    .clk_i,
    .rst_ni,
    .req_i(all_matches),
    .data_i(region_ctrls),
    .gnt_o(),
    .idx_o(),
    .valid_o(sel_match),
    .data_o(sel_region),
    .ready_i(1'b1)
  );

  // if there is a match, mask off the address bits and remap
  // if there is no match, just use incoming address
  assign addr_o = sel_match ? addr_i & sel_region.output_mask | sel_region.remap_addr :
                              addr_i;

  // unused clock/reset, only needed for assertions
  logic unused_clk;
  logic unused_rst_n;
  assign unused_clk = clk_i;
  assign unused_rst_n = rst_ni;

endmodule // rv_core_addr_trans
