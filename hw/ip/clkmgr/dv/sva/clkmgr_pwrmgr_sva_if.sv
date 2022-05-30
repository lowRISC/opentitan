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

  // Assuming io_div4 : 24MHz, AON : 200KHz
  localparam int AonCycleInClki = 120;

  // Since io_div4 and Aon is not aligned, max cycle delay
  // can be 2 + 1 cycles fo AON clk.
  localparam int UsbRiseCyclesMax = 3 * AonCycleInClki;

  bit disable_sva;

  `ASSERT(IoStatusFall_A,
          $fell(io_clk_en) |-> ##[FallCyclesMin:FallCyclesMax] io_clk_en || !io_status, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(IoStatusRise_A,
          $rose(io_clk_en) |-> ##[RiseCyclesMin:RiseCyclesMax] !io_clk_en || io_status, clk_i,
          !rst_ni || disable_sva)

  `ASSERT(MainStatusFall_A,
          $fell(main_clk_en) |-> ##[FallCyclesMin:FallCyclesMax] main_clk_en || !main_status, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(MainStatusRise_A,
          $rose(main_clk_en) |-> ##[RiseCyclesMin:RiseCyclesMax] !main_clk_en || main_status, clk_i,
          !rst_ni || disable_sva)

  `ASSERT(UsbStatusFall_A,
          $fell(usb_clk_en) |-> ##[FallCyclesMin:FallCyclesMax] usb_clk_en || !usb_status, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(UsbStatusRise_A,
          $rose(usb_clk_en) |->
          ##[RiseCyclesMin:UsbRiseCyclesMax] !usb_clk_en || usb_status, clk_i,
          !rst_ni || disable_sva)
endinterface
