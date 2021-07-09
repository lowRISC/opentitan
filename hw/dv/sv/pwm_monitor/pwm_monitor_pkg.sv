// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwm_monitor_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // datatype
  typedef enum bit [1:0] {
    Standard   = 2'b00,
    Blinking   = 2'b01,
    Heartbeat  = 2'b11
  } pwm_mode_e;

  typedef enum bit {
    PulseWrapped   = 1'b1,
    PulseNoWrapped = 1'b0
  } pwm_pulse_wrap_e;

  // package sources
  `include "pwm_item.sv"
  `include "pwm_monitor_cfg.sv"
  `include "pwm_monitor.sv"

endpackage : pwm_monitor_pkg
