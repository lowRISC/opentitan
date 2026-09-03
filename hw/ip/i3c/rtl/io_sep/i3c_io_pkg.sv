// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I/O ports for I3C signaling using two mode-specific driver enables.
//
// Driver Style 1 (see ./doc/integration_notes.md)
// - Separated Push-Pull and Open Drain enable outputs.

package i3c_io_pkg;
  import i3c_pkg::*;

  // Separated enable signals for push-pull and open drain drivers.
  parameter bit DrvSeparatedEn = 1'b1;

  // State of Controller driver enables.
  typedef struct {
    logic pp_en;  // Push-pull driver enable.
    logic od_en;  // Open drain driver enable.
    logic pu_en;  // Pull-up enable.
  } drv_state_t;

  // Return the appropriate driver state for Open Drain signaling.
  // - pull up is enabled, driver is enabled and may pull down.
  function automatic drv_state_t open_drain;
    drv_state_t drv;
    drv.pp_en = 1'b0;
    drv.od_en = 1'b1;
    drv.pu_en = 1'b1;
    return drv;
  endfunction

  // Return the appropriate driver state for Open Drain reception.
  // - pull-up is enabled, but not the open drain driver.
  function automatic drv_state_t pull_up;
    drv_state_t drv;
    drv.pp_en = 1'b0;
    drv.od_en = 1'b0;
    drv.pu_en = 1'b1;
    return drv;
  endfunction

  // Return the appropriate driver state for Push-Pull signaling.
  function automatic drv_state_t push_pull;
    drv_state_t drv;
    drv.pp_en = 1'b1;
    drv.od_en = 1'b0;
    drv.pu_en = 1'b0;
    return drv;
  endfunction

  // Disconnect from the I3C bus entirely; Hi-Z.
  function automatic drv_state_t disconnect;
    drv_state_t drv;
    drv.pp_en = 1'b0;
    drv.od_en = 1'b0;
    drv.pu_en = 1'b0;
    return drv;
  endfunction

  // Controller-side driver signals.
  typedef struct {
    logic scl_en;
    logic scl;
    logic sda_pp_en;
    logic sda_od_en;
    logic [NumSDALanes-1:0] sda;
  } i3c_ctrl_bus_drv_t;

  // Target-side driver signals.
  typedef struct {
    logic sda_pp_en;
    logic sda_od_en;
    logic [NumSDALanes-1:0] sda;
  } i3c_targ_bus_drv_t;

  // Observed bus signals on the Controller side.
  typedef struct {
  logic scl;
  logic [NumSDALanes-1:0] sda;
  } i3c_ctrl_bus_obs_t;

  // Observed bus signals on the Target side.
  typedef struct {
  logic scl;
  logic [NumSDALanes-1:0] sda;
  } i3c_targ_bus_obs_t;

endpackage
