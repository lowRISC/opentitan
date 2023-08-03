// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module mbx
  import tlul_pkg::*;
(
  input  logic                  clk_i,
  input  logic                  rst_ni,
  output logic                  irq_o,
  // Device port facing OT-host
  input   tlul_pkg::tl_h2d_t    tl_host_i,
  output  tlul_pkg::tl_d2h_t    tl_host_o,
  // Device port facing CTN Xbar
  input   tlul_pkg::tl_h2d_t    tl_sys_i,
  output  tlul_pkg::tl_d2h_t    tl_sys_o,
  // Host port to access private SRAM
  input   tlul_pkg::tl_d2h_t    tl_sram_i,
  output  tlul_pkg::tl_h2d_t    tl_sram_o
);

endmodule
