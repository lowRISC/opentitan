// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements controls for the simulation SRAM in an interface so that the UVM world can directly
// manipulate it.
interface sim_sram_if #(
    parameter int AddrWidth = 32
) (
    input clk_i,
    input tlul_pkg::tl_h2d_t tl_i
);

  // SRAM start addr - set by the testbench.
  bit [AddrWidth-1:0] start_addr;

endinterface
