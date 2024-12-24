// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions to check that rising or falling edges of a clock's ip_clk_en
// is followed by corresponding edges of its clk_status.
interface clkmgr_pwrmgr_sva_if #(
  parameter int IS_USB = 0
) (
  input logic clk_i,
  input logic rst_ni,
  input logic clk_en,
  input logic status
);

  // The max times are longer to cover the different clock domain synchronizers.
  // Ideally they would use the io_div4 clock, but it gets turned off when io_ip_clk_en
  // goes inactive.
  localparam int FallCyclesMin = 0;
  localparam int FallCyclesMax = 20;

  // Assuming io_div4 : 24MHz, AON : 200KHz
  localparam int AonCycleInClki = 120;

  // Since io_div4 and Aon is not aligned, max cycle delay
  // can be 2 + 1 cycles fo AON clk.
  localparam int UsbRiseCyclesMax = 3 * AonCycleInClki;

  localparam int RiseCyclesMin = 0;
  localparam int RiseCyclesMax = IS_USB ? UsbRiseCyclesMax : 20;

  bit disable_sva;

  `ASSERT(StatusFall_A,
          $fell(clk_en) |-> ##[FallCyclesMin:FallCyclesMax] clk_en || !status, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(StatusRise_A,
          $rose(clk_en) |-> ##[RiseCyclesMin:RiseCyclesMax] !clk_en || status, clk_i,
          !rst_ni || disable_sva)
endinterface
