// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions to check losing calibration turns off clock measurements.

interface clkmgr_lost_calib_ctrl_en_sva_if (
  input logic clk,
  input logic rst_n,
  input logic [$bits(prim_mubi_pkg::mubi4_t)-1:0] calib_rdy,
  input logic [$bits(prim_mubi_pkg::mubi4_t)-1:0] meas_ctrl_en
);
  // There are two clocks involved, the clock measured and the clkmgr clk_i.
  // The latter is io_div4 so it is pretty slow compared to all others. There
  // are a number of clock domain crossings, so this needs a large number of
  // wait cycles to account for the worst case.
  localparam int MAX_CYCLES = 45;
  `ASSERT(CtrlEnOn_A,
          (calib_rdy == prim_mubi_pkg::MuBi4False && meas_ctrl_en != prim_mubi_pkg::MuBi4False) |=>
          ##[0:MAX_CYCLES] (meas_ctrl_en == prim_mubi_pkg::MuBi4False),
          clk, !rst_n)
endinterface
