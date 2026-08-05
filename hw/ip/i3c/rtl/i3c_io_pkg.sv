// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I/O ports for I3C signaling.
// - the specific signals used may depend upon the deployment, e.g. the I/O drivers available.

package i3c_io_pkg;
  import i3c_pkg::*;

  // Separated Push-Pull and Open Drain enable outputs.
  //
  // TODO: Find an alternative way to choose among the various implementations.
  // The use of conditional_generate_constructs ('if') is not permitted within packages.
  `ifndef I3C_DRV_SEPARATED_DEFINED
    `define I3C_DRV_SEPARATED_EN
  `endif

  `ifdef I3C_DRV_SEPARATED_EN
    parameter bit DrvSeparatedEn = 1'b1;

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
      logic [NumSDALanes-1:0] sda;
      logic sda_pp_en;
      logic sda_od_en;
    } i3c_targ_bus_drv_t;
  `else
    parameter bit DrvSeparatedEn = 1'b0;

    // Controller-side driver signals.
    typedef struct {
      logic scl;
      logic scl_en;
      logic sda_en;
      logic sda_pp_mode;
      logic [NumSDALanes-1:0] sda;
    } i3c_ctrl_bus_drv_t;

    // Target-side driver signals.
    typedef struct {
      logic sda_en;
      logic sda_pp_mode;
      logic [NumSDALanes-1:0] sda;
    } i3c_targ_bus_drv_t;
  `endif

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
