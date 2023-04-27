// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has some assertions that check clock and main pd behavior at the top-level,
// especially as it relates to the ast and pwrmgr interaction.
interface clk_ctrl_and_main_pd_sva_if (
  input logic clk_slow_i,
  input logic rst_slow_ni,
  // por for domain zero.
  input logic por_d0_ni,
  // The pwrmgr clk handshake.
  input logic core_clk_en,
  input logic core_clk_val,
  input logic clk_core_i,
  input logic io_clk_en,
  input logic io_clk_val,
  input logic clk_io_i,
  input logic usb_clk_en,
  input logic usb_clk_val,
  input logic clk_usb_i,
  input logic main_pd_n,
  input logic main_pok
);

  // These numbers of cycles are meant to match both the randomization in
  // pwrmgr_base_vseq, and the actual cycle counts from full chip.
  // Notice the expectation for full chip is that deassertion of *clk_val
  // takes 0 cycles, and assertion takes a 2 cycle synchronizer delay on
  // the slow clock; deassertion of main_pok takes one cycle, and assertion
  // not more than 2 cycles.
  localparam int MIN_CLK_WAIT_CYCLES = 0;
  localparam int MIN_PDN_WAIT_CYCLES = 0;
  localparam int MAX_CLK_WAIT_CYCLES = 60;
  localparam int MAX_PDN_WAIT_CYCLES = 110;

  bit disable_sva;
  bit reset_or_disable;

  always_comb reset_or_disable = !rst_slow_ni || disable_sva;

  `define CLK_WAIT_BOUNDS ##[MIN_CLK_WAIT_CYCLES:MAX_CLK_WAIT_CYCLES]
  `define PDN_WAIT_BOUNDS ##[MIN_PDN_WAIT_CYCLES:MAX_PDN_WAIT_CYCLES]

  // Changes triggered by por_d0_ni only affect clk_val.
  `ASSERT(CoreClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:1] !core_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(CoreClkGlitchToValOn_A, $rose(por_d0_ni) && core_clk_en |-> ##[0:2] core_clk_val,
          clk_slow_i, reset_or_disable)
  `ASSERT(IoClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:1] !io_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(IoClkGlitchToValOn_A, $rose(por_d0_ni) && io_clk_en |-> ##[0:2] io_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(UsbClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:5] !usb_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(UsbClkGlitchToValOn_A, $rose(por_d0_ni) && usb_clk_en |-> ##[0:5] usb_clk_val, clk_slow_i,
          reset_or_disable)

  // Changes not triggered by por_d0_ni
  `ASSERT(CoreClkHandshakeOn_A,
          $rose(core_clk_en) && por_d0_ni |-> `CLK_WAIT_BOUNDS
          core_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(CoreClkHandshakeOff_A, $fell(core_clk_en) |-> `CLK_WAIT_BOUNDS !core_clk_val, clk_slow_i,
          reset_or_disable)

  `ASSERT(IoClkHandshakeOn_A,
          $rose(io_clk_en) && por_d0_ni |-> `CLK_WAIT_BOUNDS
          io_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(IoClkHandshakeOff_A, $fell(io_clk_en) |-> `CLK_WAIT_BOUNDS !io_clk_val, clk_slow_i,
          reset_or_disable)

  // Usb is a bit different: apparently usb_clk_val can stay low after a power glitch, so it may
  // already be low when usb_clk_en drops.
  `ASSERT(UsbClkHandshakeOn_A,
          $rose(usb_clk_en) && por_d0_ni && $past(por_d0_ni, 1) |-> `CLK_WAIT_BOUNDS
          usb_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(UsbClkHandshakeOff_A, $fell(usb_clk_en) |-> `CLK_WAIT_BOUNDS !usb_clk_val, clk_slow_i,
          reset_or_disable)

  int main_clk_cycles, io_clk_cycles, usb_clk_cycles;
  always_ff @(posedge clk_core_i) main_clk_cycles++;
  always_ff @(posedge clk_io_i) io_clk_cycles++;
  always_ff @(posedge clk_usb_i) usb_clk_cycles++;

  `ASSERT(MainClkStopped_A,
          $fell(core_clk_val) |=> ($stable(main_clk_cycles) || core_clk_val) [* 1 : $], clk_slow_i,
          reset_or_disable)
  `ASSERT(MainClkRun_A,
          $rose(core_clk_val) |=> (!$stable(main_clk_cycles) || !core_clk_val) [* 1 : $],
          clk_slow_i, reset_or_disable)

  `ASSERT(IOClkStopped_A, $fell(io_clk_val) |=> ($stable(io_clk_cycles) || io_clk_val) [* 1 : $],
          clk_slow_i, reset_or_disable)
  `ASSERT(IOClkRun_A, $rose(io_clk_val) |=> (!$stable(io_clk_cycles) || !io_clk_val) [* 1 : $],
          clk_slow_i, reset_or_disable)

  `ASSERT(USBClkStopped_A,
          $fell(usb_clk_val) |=> ($stable(usb_clk_cycles) || usb_clk_val) [* 1 : $], clk_slow_i,
          reset_or_disable)
  `ASSERT(USBClkRun_A, $rose(usb_clk_val) |=> (!$stable(usb_clk_cycles) || !usb_clk_val) [* 1 : $],
          clk_slow_i, reset_or_disable)

  // Main pd-pok
  `ASSERT(MainPdHandshakeOn_A, main_pd_n |-> `PDN_WAIT_BOUNDS main_pok, clk_slow_i,
          reset_or_disable)
  `ASSERT(MainPdHandshakeOff_A, !main_pd_n |-> `PDN_WAIT_BOUNDS !main_pok, clk_slow_i,
          reset_or_disable)

  `undef CLK_WAIT_BOUNDS
  `undef PDN_WAIT_BOUNDS
endinterface
