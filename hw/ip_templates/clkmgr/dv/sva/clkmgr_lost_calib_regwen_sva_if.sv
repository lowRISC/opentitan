// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions to check losing calibration enables crtl regwen.

interface clkmgr_lost_calib_regwen_sva_if (
  input logic clk,
  input logic rst_n,
  input prim_mubi_pkg::mubi4_t calib_rdy,
  input logic meas_ctrl_regwen
);
  localparam int MAX_CYCLES = 6;
  `ASSERT(RegwenOff_A,
          (calib_rdy == prim_mubi_pkg::MuBi4False) |=> ##[0:MAX_CYCLES] meas_ctrl_regwen, clk,
          !rst_n)
endinterface
