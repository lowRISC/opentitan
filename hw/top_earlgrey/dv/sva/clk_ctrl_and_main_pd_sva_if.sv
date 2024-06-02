// Copyright lowRISC contributors (OpenTitan project).
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
  localparam int MIN_CLK_ON_WAIT_CYCLES = 0;
  localparam int MIN_PDN_WAIT_CYCLES = 0;
  localparam int MAX_CLK_ON_WAIT_CYCLES = 60;
  localparam int MAX_PDN_WAIT_CYCLES = 160;

  `define CLK_ON_WAIT_BOUNDS ##[MIN_CLK_ON_WAIT_CYCLES:MAX_CLK_ON_WAIT_CYCLES]
  `define PDN_WAIT_BOUNDS ##[MIN_PDN_WAIT_CYCLES:MAX_PDN_WAIT_CYCLES]

  // The time to turn clocks off is up to 4 slow clock cycles.
  localparam int CLK_OFF_WAIT_CYCLES = 4;

  bit disable_sva;
  bit reset_or_disable;

  always_comb reset_or_disable = !rst_slow_ni || disable_sva;

  // Changes triggered by por_d0_ni only affect clk_val.
  `ASSERT(CoreClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:1] !core_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(CoreClkGlitchToValOn_A, $rose(por_d0_ni) && core_clk_en |->
          `CLK_ON_WAIT_BOUNDS core_clk_val, clk_slow_i, reset_or_disable)
  `ASSERT(IoClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:1] !io_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(IoClkGlitchToValOn_A, $rose(por_d0_ni) && io_clk_en |-> `CLK_ON_WAIT_BOUNDS io_clk_val,
          clk_slow_i, reset_or_disable)
  `ASSERT(UsbClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:5] !usb_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(UsbClkGlitchToValOn_A, $rose(por_d0_ni) && usb_clk_en |-> `CLK_ON_WAIT_BOUNDS usb_clk_val,
          clk_slow_i, reset_or_disable)

  // Changes not triggered by por_d0_ni
  `ASSERT(CoreClkHandshakeOn_A,
          $rose(core_clk_en) && por_d0_ni |-> `CLK_ON_WAIT_BOUNDS
          core_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(CoreClkHandshakeOff_A, $fell(core_clk_en) |-> ##CLK_OFF_WAIT_CYCLES !core_clk_val,
          clk_slow_i, reset_or_disable)

  `ASSERT(IoClkHandshakeOn_A,
          $rose(io_clk_en) && por_d0_ni |-> `CLK_ON_WAIT_BOUNDS
          io_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(IoClkHandshakeOff_A, $fell(io_clk_en) |-> ##CLK_OFF_WAIT_CYCLES !io_clk_val, clk_slow_i,
          reset_or_disable)

  // Usb is a bit different: apparently usb_clk_val can stay low after a power glitch, so it may
  // already be low when usb_clk_en drops.
  `ASSERT(UsbClkHandshakeOn_A,
          $rose(usb_clk_en) && por_d0_ni && $past(por_d0_ni, 1) |-> `CLK_ON_WAIT_BOUNDS
          usb_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(UsbClkHandshakeOff_A, $fell(usb_clk_en) |-> ##CLK_OFF_WAIT_CYCLES !usb_clk_val,
          clk_slow_i, reset_or_disable)

  // Check when the clocks are meant to be active or stopped. For each clock we create two pairs of
  // assertions:
  // 1. Expect the clock to become inactive after a few aon cycles when clk_en or clk_val drop.
  // 2. Expect the clock to become active when clk_en or clk_val raises.
  int main_clk_cycles, io_clk_cycles, usb_clk_cycles;
  always_ff @(posedge clk_core_i) main_clk_cycles++;
  always_ff @(posedge clk_io_i) io_clk_cycles++;
  always_ff @(posedge clk_usb_i) usb_clk_cycles++;

  `ASSERT(MainClkEnStart_A,
          $rose(core_clk_en) |=> `CLK_ON_WAIT_BOUNDS  !core_clk_en || !$stable(main_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(MainClkValStart_A,
          $rose(core_clk_val) |=> `CLK_ON_WAIT_BOUNDS !core_clk_val || !$stable(main_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(MainClkEnStop_A,
          $fell(core_clk_en) |=> ##CLK_OFF_WAIT_CYCLES core_clk_en || $stable(main_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(MainClkValStop_A,
          $fell(core_clk_val) |=> ##CLK_OFF_WAIT_CYCLES core_clk_val || $stable(main_clk_cycles),
          clk_slow_i, reset_or_disable)

  `ASSERT(IOClkEnStart_A,
          $rose(io_clk_en) |=> `CLK_ON_WAIT_BOUNDS  !io_clk_en || !$stable(io_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(IOClkValStart_A,
          $rose(io_clk_val) |=> `CLK_ON_WAIT_BOUNDS !io_clk_val || !$stable(io_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(IOClkEnStop_A,
          $fell(io_clk_en) |=> ##CLK_OFF_WAIT_CYCLES io_clk_en || $stable(io_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(IOClkValStop_A,
          $fell(io_clk_val) |=> ##CLK_OFF_WAIT_CYCLES io_clk_val || $stable(io_clk_cycles),
          clk_slow_i, reset_or_disable)

  `ASSERT(USBClkEnStart_A,
          $rose(usb_clk_en) |=> `CLK_ON_WAIT_BOUNDS !usb_clk_en || !$stable(usb_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(USBClkValStart_A,
          $rose(usb_clk_val) |=> `CLK_ON_WAIT_BOUNDS !usb_clk_val || !$stable(usb_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(USBClkEnStop_A,
          $fell(usb_clk_en) |=> ##CLK_OFF_WAIT_CYCLES usb_clk_en || $stable(usb_clk_cycles),
          clk_slow_i, reset_or_disable)
  `ASSERT(USBClkValStop_A,
          $fell(usb_clk_val) |=> ##CLK_OFF_WAIT_CYCLES usb_clk_val || $stable(usb_clk_cycles),
          clk_slow_i, reset_or_disable)

  // Main pd-pok
  `ASSERT(MainPdHandshakeOn_A, main_pd_n |-> `PDN_WAIT_BOUNDS main_pok, clk_slow_i,
          reset_or_disable)
  `ASSERT(MainPdHandshakeOff_A, !main_pd_n |-> `PDN_WAIT_BOUNDS !main_pok, clk_slow_i,
          reset_or_disable)

  `undef CLK_WAIT_BOUNDS
  `undef PDN_WAIT_BOUNDS
endinterface
