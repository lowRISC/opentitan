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

  // local types

  // forward declare classes to allow typedefs below
  typedef class pwm_item;
  typedef class pwm_monitor_cfg;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(pwm_item),
                              .CFG_T (pwm_monitor_cfg)) pwm_sequencer;

  // functions

  // package sources
  `include "pwm_item.sv"
  `include "pwm_monitor_cfg.sv"
  `include "pwm_monitor.sv"

endpackage: pwm_monitor_pkg
