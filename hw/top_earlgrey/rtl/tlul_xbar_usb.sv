// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: Only here until code is ported to use top generator
module tlul_xbar_usb (
  input clk_i,
  input rst_ni,

  // Host accepter
  input  tlul_pkg::tl_h2d_t tl_h_i [tl_main_pkg::N_HOST],
  output tlul_pkg::tl_d2h_t tl_h_o [tl_main_pkg::N_HOST],

  // Device sender
  output tlul_pkg::tl_h2d_t tl_d_o [tl_main_pkg::N_DEVICE],
  input  tlul_pkg::tl_d2h_t tl_d_i [tl_main_pkg::N_DEVICE]
);

  import tlul_pkg::*;
  import tl_main_pkg::*;

  //
  // Core D interface connects to Sram, Uart, Gpio, DebugMem and error
  //
  localparam int unsigned N_CORE_D_DEVICE = 5;

  typedef enum logic [2:0] {
    CoreDToSram     = 3'h0,
    CoreDToUart     = 3'h1,
    CoreDToGpio     = 3'h2,
    CoreDToDebugMem = 3'h3,
    CoreDToSpiDevice = 3'h4,
    CoreDToErr      = 3'h5
  } core_d_dsp_e;

  core_d_dsp_e dev_select_core_d;

  tl_h2d_t tl_core_d_h2d [N_CORE_D_DEVICE];
  tl_d2h_t tl_core_d_d2h [N_CORE_D_DEVICE];

  tlul_socket_1n #(
    .N            (N_CORE_D_DEVICE),
    .HReqPass     (1'b0),                     // register just outside of core
    .HRspPass     (1'b0),                     // register just outside of core
    .DReqPass     ({N_CORE_D_DEVICE{1'b1}}),  // unregistered
    .DRspPass     ({N_CORE_D_DEVICE{1'b1}}),  // unregistered
    .HReqDepth    (4'h2),                     // some elasticity
    .HRspDepth    (4'h2),                     // some elasticity
    .DReqDepth    ({N_CORE_D_DEVICE{4'h1}}),  // minimal elasticity
    .DRspDepth    ({N_CORE_D_DEVICE{4'h1}})   // minimal elasticity
  ) core_d_socket_14 (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .tl_h_i       (tl_h_i[TlCored]),
    .tl_h_o       (tl_h_o[TlCored]),
    .tl_d_o       (tl_core_d_h2d),
    .tl_d_i       (tl_core_d_d2h),
    .dev_select   (dev_select_core_d)
  );

  // address map lookup, will eventually be automated via configuration
  assign dev_select_core_d =
      ((tl_h_i[TlCored].a_address & ~ADDR_MASK_RAM_MAIN)     == ADDR_SPACE_RAM_MAIN)     ? CoreDToSram :
      ((tl_h_i[TlCored].a_address & ~ADDR_MASK_UART)     == ADDR_SPACE_UART)     ? CoreDToUart :
      ((tl_h_i[TlCored].a_address & ~ADDR_MASK_GPIO)     == ADDR_SPACE_GPIO)     ? CoreDToGpio :
      ((tl_h_i[TlCored].a_address & ~ADDR_MASK_DEBUG_MEM) == ADDR_SPACE_DEBUG_MEM) ? CoreDToDebugMem :
      ((tl_h_i[TlCored].a_address & ~ADDR_MASK_SPI_DEVICE)     == ADDR_SPACE_SPI_DEVICE)     ? CoreDToSpiDevice :
          CoreDToErr; // indicate to socket to return error


  //
  // Core I connects to SRAM and Debug Memory and error
  // TODO: Add connection to bootrom
  //
  localparam int unsigned N_CORE_I_DEVICE = 2;

  typedef enum logic [1:0] {
    CoreIToSram     = 2'h0,
    CoreIToDebugMem = 2'h1,
    CoreIToErr      = 2'h2
  } core_i_dsp_e;

  core_i_dsp_e dev_select_core_i;

  tl_h2d_t tl_core_i_h2d [N_CORE_I_DEVICE];
  tl_d2h_t tl_core_i_d2h [N_CORE_I_DEVICE];

  tlul_socket_1n #(
    .N            (N_CORE_I_DEVICE),
    .HReqPass     (1'b0),                     // register just outside of core
    .HRspPass     (1'b0),                     // register just outside of core
    .DReqPass     ({N_CORE_I_DEVICE{1'b1}}),  // unregistered
    .DRspPass     ({N_CORE_I_DEVICE{1'b1}}),  // unregistered
    .HReqDepth    (4'h2),                     // some elasticity
    .HRspDepth    (4'h2),                     // some elasticity
    .DReqDepth    ({N_CORE_I_DEVICE{4'h1}}),  // minimal elasticity
    .DRspDepth    ({N_CORE_I_DEVICE{4'h1}})   // minimal elasticity
    ) core_i_socket_12 (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .tl_h_i       (tl_h_i[TlCorei]),
    .tl_h_o       (tl_h_o[TlCorei]),
    .tl_d_o       (tl_core_i_h2d),
    .tl_d_i       (tl_core_i_d2h),
    .dev_select   (dev_select_core_i)
    );

  // address map lookup, will eventually be automated via configuration
  assign dev_select_core_i =
    ((tl_h_i[TlCorei].a_address & ~ADDR_MASK_RAM_MAIN)     == ADDR_SPACE_RAM_MAIN)     ? CoreIToSram :
    ((tl_h_i[TlCorei].a_address & ~ADDR_MASK_DEBUG_MEM) == ADDR_SPACE_DEBUG_MEM) ? CoreIToDebugMem :
    CoreIToErr; // indicate to socket to return error


  //
  // SRAM connects to Core I, Core D and Debug SBA
  //
  localparam int unsigned N_SRAM_HOST = 3;

  typedef enum logic [1:0] {
    SramFromCoreI    = 2'h0,
    SramFromCoreD    = 2'h1,
    SramFromDebugSba = 2'h2
  } sram_host_e;

  tl_h2d_t tl_sram_h_h2d [N_SRAM_HOST];
  tl_d2h_t tl_sram_h_d2h [N_SRAM_HOST];

  assign tl_sram_h_h2d[SramFromCoreI]    = tl_core_i_h2d[CoreIToSram];
  assign tl_sram_h_h2d[SramFromCoreD]    = tl_core_d_h2d[CoreDToSram];
  assign tl_sram_h_h2d[SramFromDebugSba] = tl_h_i[TlDmSba];

  assign tl_core_i_d2h[CoreIToSram] = tl_sram_h_d2h[SramFromCoreI];
  assign tl_core_d_d2h[CoreDToSram] = tl_sram_h_d2h[SramFromCoreD];
  assign tl_h_o[TlDmSba]         = tl_sram_h_d2h[SramFromDebugSba];

  tlul_socket_m1 #(
    .M            (N_SRAM_HOST),
    .HReqPass     ({N_SRAM_HOST{1'b1}}),   // unregistered
    .HRspPass     ({N_SRAM_HOST{1'b1}}),   // unregistered
    .HReqDepth    ({N_SRAM_HOST{4'h1}}),   // minimal elasticity
    .HRspDepth    ({N_SRAM_HOST{4'h1}}),   // minimal elasticity
    .DReqPass     (1'b1),                  // unregistered
    .DRspPass     (1'b1),                  // unregistered
    .DReqDepth    (4'h1),                  // minimal elasticity
    .DRspDepth    (4'h1)                   // minimal elasticity
  ) sram_socket_31 (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .tl_h_i       (tl_sram_h_h2d),
    .tl_h_o       (tl_sram_h_d2h),
    .tl_d_o       (tl_d_o[TlRamMain]),
    .tl_d_i       (tl_d_i[TlRamMain])
  );


  //
  // Debug Memory connects to Core I and Core D
  //
  localparam int unsigned N_DEBUGMEM_HOST = 2;

  typedef enum logic [0:0] {
    DebugMemFromCoreI = 1'h0,
    DebugMemFromCoreD = 1'h1
  } debugmem_host_e;

  tl_h2d_t tl_debugmem_h_h2d [N_DEBUGMEM_HOST];
  tl_d2h_t tl_debugmem_h_d2h [N_DEBUGMEM_HOST];

  assign tl_debugmem_h_h2d[DebugMemFromCoreI] = tl_core_i_h2d[CoreIToDebugMem];
  assign tl_debugmem_h_h2d[DebugMemFromCoreD] = tl_core_d_h2d[CoreDToDebugMem];

  assign tl_core_i_d2h[CoreIToDebugMem] = tl_debugmem_h_d2h[DebugMemFromCoreI];
  assign tl_core_d_d2h[CoreDToDebugMem] = tl_debugmem_h_d2h[DebugMemFromCoreD];

  tlul_socket_m1 #(
    .M            (N_DEBUGMEM_HOST),
    .HReqPass     ({N_DEBUGMEM_HOST{1'b1}}), // unregistered
    .HRspPass     ({N_DEBUGMEM_HOST{1'b1}}), // unregistered
    .HReqDepth    ({N_DEBUGMEM_HOST{4'h1}}), // minimal elasticity
    .HRspDepth    ({N_DEBUGMEM_HOST{4'h1}}), // minimal elasticity
    .DReqPass     (1'b1),                    // unregistered
    .DRspPass     (1'b1),                    // unregistered
    .DReqDepth    (4'h1),                    // minimal elasticity
    .DRspDepth    (4'h1)                     // minimal elasticity
  ) debugmem_socket_21 (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .tl_h_i       (tl_debugmem_h_h2d),
    .tl_h_o       (tl_debugmem_h_d2h),
    .tl_d_o       (tl_d_o[TlDebugMem]),
    .tl_d_i       (tl_d_i[TlDebugMem])
  );


  // UART connects to Core D
  // TODO: Connect to SBA as well?
  assign tl_d_o[TlUart] = tl_core_d_h2d[CoreDToUart];
  assign tl_core_d_d2h[CoreDToUart] = tl_d_i[TlUart];

  // GPIO connects to Core D
  // TODO: Connect to SBA as well?
  assign tl_d_o[TlGpio] = tl_core_d_h2d[CoreDToGpio];
  assign tl_core_d_d2h[CoreDToGpio] = tl_d_i[TlGpio];

  // SPI Device
  assign tl_d_o[TlSpiDevice] = tl_core_d_h2d[CoreDToSpiDevice];
  assign tl_core_d_d2h[CoreDToSpiDevice] = tl_d_i[TlSpiDevice];
endmodule
