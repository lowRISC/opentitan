// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rv_timer_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import rv_timer_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Dummy objects used to derive the actual size from structs in rv_timer_reg_pkg
  rv_timer_reg_pkg::rv_timer_reg2hw_cfg0_reg_t           cfg0_fields;
  rv_timer_reg_pkg::rv_timer_reg2hw_timer_v_lower0_reg_t timer_v_lower0;
  rv_timer_reg_pkg::rv_timer_reg2hw_timer_v_upper0_reg_t timer_v_upper0;

  // Widths of WKUP/WDOG counters/threshold registers, respectively.
  localparam int unsigned PRESCALER_WIDTH  = $bits(cfg0_fields.prescale.q);
  localparam int unsigned STEP_WIDTH       = $bits(cfg0_fields.step.q);
  localparam int unsigned MTIME_WIDTH      = $bits(timer_v_lower0.q) + $bits(timer_v_upper0.q);


  // local parameters and types
  // These are currently hardcoded to 1 - this will need to change if design is modified
  parameter uint NUM_HARTS = 1;
  parameter uint NUM_TIMERS = 1;

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault"};

  typedef class rv_timer_env_cfg;
  typedef class rv_timer_env_cov;
  typedef cip_base_virtual_sequencer #(rv_timer_env_cfg,
                                       rv_timer_env_cov) rv_timer_virtual_sequencer;

  // functions

  // package sources
  `include "rv_timer_env_cfg.sv"
  `include "rv_timer_env_cov.sv"
  `include "rv_timer_scoreboard.sv"
  `include "rv_timer_env.sv"
  `include "rv_timer_vseq_list.sv"
endpackage
