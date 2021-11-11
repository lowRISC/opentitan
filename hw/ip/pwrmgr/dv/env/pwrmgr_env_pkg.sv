// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwrmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import pwrmgr_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // types
  typedef enum int {
    WakeupSysrst,
    WakeupDbgCable,
    WakeupAon,
    WakeupUsb,
    WakeupAonTimer
  } wakeup_e;

  typedef struct packed {
    logic main_pd_n;
    logic usb_clk_en_active;
    logic usb_clk_en_lp;
    logic io_clk_en;
    logic core_clk_en;
  } control_enables_t;

  typedef bit [pwrmgr_reg_pkg::NumWkups-1:0] wakeups_t;
  typedef bit [pwrmgr_reg_pkg::NumRstReqs-1:0] resets_t;

  // functions

  // package sources
  `include "pwrmgr_env_cfg.sv"
  `include "pwrmgr_env_cov.sv"
  `include "pwrmgr_virtual_sequencer.sv"
  `include "pwrmgr_scoreboard.sv"
  `include "pwrmgr_env.sv"
  `include "pwrmgr_vseq_list.sv"

endpackage
