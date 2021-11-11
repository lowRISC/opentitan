// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions to check that rising or falling edges of the various ip_clk_en
// are followed by corresponding edges of their clk_status.
interface clkmgr_pwrmgr_sva_if (
  input logic clk_i,
  input logic rst_ni,
  input logic io_clk_en,
  input logic io_status,
  input logic main_clk_en,
  input logic main_status,
  input logic usb_clk_en,
  input logic usb_status
);

  // The max times are longer to cover the different clock domain synchronizers.
  // Ideally they would use the io_div4 clock, but it gets turned off when io_ip_clk_en
  // goes inactive.
  localparam int FallCyclesMin = 0;
  localparam int FallCyclesMax = 16;

  localparam int RiseCyclesMin = 0;
  localparam int RiseCyclesMax = 16;

  bit disable_sva;

  `ASSERT(IoStatusFall_A, $fell(io_clk_en) |-> ##[FallCyclesMin:FallCyclesMax] $fell(io_status),
          clk_i, !rst_ni || disable_sva)
  `ASSERT(IoStatusRise_A, $rose(io_clk_en) |-> ##[RiseCyclesMin:RiseCyclesMax] $rose(io_status),
          clk_i, !rst_ni || disable_sva)

  `ASSERT(MainStatusFall_A,
          $fell(main_clk_en) |-> ##[FallCyclesMin:FallCyclesMax] $fell(main_status), clk_i,
          !rst_ni || disable_sva)
  `ASSERT(MainStatusRise_A,
          $rose(main_clk_en) |-> ##[RiseCyclesMin:RiseCyclesMax] $rose(main_status), clk_i,
          !rst_ni || disable_sva)

  `ASSERT(UsbStatusFall_A, $fell(usb_clk_en) |-> ##[FallCyclesMin:FallCyclesMax] $fell(usb_status),
          clk_i, !rst_ni || disable_sva)
  `ASSERT(UsbStatusRise_A, $rose(usb_clk_en) |-> ##[RiseCyclesMin:RiseCyclesMax] $rose(usb_status),
          clk_i, !rst_ni || disable_sva)
endinterface
