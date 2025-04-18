// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aon_timer_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import aon_timer_ral_pkg::*;
  import usbdev_env_pkg::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault"};

  // Dummy objects used to derive the actual size from structs in aon_timer_reg_pkg
  aon_timer_reg_pkg::aon_timer_reg2hw_wkup_ctrl_reg_t     wkup_ctrl_fields;
  aon_timer_reg_pkg::aon_timer_reg2hw_wkup_count_hi_reg_t wkup_count_hi;
  aon_timer_reg_pkg::aon_timer_reg2hw_wkup_count_lo_reg_t wkup_count_lo;
  aon_timer_reg_pkg::aon_timer_reg2hw_wdog_count_reg_t    wdog_count;

  // Widths of WKUP/WDOG counters/threshold registers, respectively.
  parameter int unsigned WKUP_WIDTH      = $bits(wkup_count_hi.q) + $bits(wkup_count_lo.q);
  parameter int unsigned WDOG_WIDTH      = $bits(wdog_count.q);
  parameter int unsigned PRESCALER_WIDTH = $bits(wkup_ctrl_fields.prescaler.q);

  // package sources
  `include "aon_timer_env_cfg.sv"
  `include "aon_timer_env_cov.sv"
  `include "aon_timer_virtual_sequencer.sv"
  `include "aon_timer_intr_timed_regs.sv"
  `include "aon_timer_scoreboard.sv"
  `include "aon_timer_env.sv"
  `include "aon_timer_vseq_list.sv"

endpackage
