// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwm_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_PWM_CHANNELS = 6;

  // local types

  // forward declare classes to allow typedefs below
  typedef class pwm_item;
  typedef class pwm_agent_cfg;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(pwm_item),
                              .CFG_T (pwm_agent_cfg)) pwm_sequencer;

  // functions

  // package sources
  `include "pwm_item.sv"
  `include "pwm_agent_cfg.sv"
  `include "pwm_agent_cov.sv"
  `include "pwm_driver.sv"
  `include "pwm_monitor.sv"
  `include "pwm_agent.sv"

endpackage: pwm_agent_pkg
