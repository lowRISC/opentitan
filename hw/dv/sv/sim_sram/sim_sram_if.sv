// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements controls for the simulation SRAM in an interface so that the UVM world can directly
// manipulate it.
interface sim_sram_if #(
  parameter int AddrWidth = 32
) (
  input logic clk_i,
  input logic rst_ni,
  input tlul_pkg::tl_h2d_t tl_h2d,
  input tlul_pkg::tl_d2h_t tl_d2h
);

  // SRAM start addr - set by the testbench.
  logic [AddrWidth-1:0] start_addr;

  // Qualify writes to the sim SRAM.
  logic wr_valid;
  assign wr_valid = tl_h2d.a_mask == '1 && tl_h2d.a_valid && tl_d2h.a_ready &&
                    tl_h2d.a_opcode == tlul_pkg::PutFullData;

endinterface
