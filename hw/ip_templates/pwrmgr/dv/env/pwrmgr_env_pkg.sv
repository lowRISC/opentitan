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
  import alert_esc_agent_pkg::*;
  import pwrmgr_pkg::PowerDomains;
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4Width;
  import sec_cm_pkg::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter int NUM_INTERRUPTS = 1;

  // clk enable disable delay
  parameter uint MAIN_CLK_DELAY_MIN = 15;
  parameter uint MAIN_CLK_DELAY_MAX = 258;
  parameter uint ESC_CLK_DELAY_MIN = 1;
  parameter uint ESC_CLK_DELAY_MAX = 10;

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // types
  typedef enum int {
    WakeupSysrst,
    WakeupDbgCable,
    WakeupPin,
    WakeupUsb,
    WakeupAonTimer,
    WakeupSensorCtrl
  } wakeup_e;

  typedef enum int {
    PwrmgrMubiNone = 0,
    PwrmgrMubiLcCtrl = 1,
    PwrmgrMubiRomCtrl = 2
  } pwrmgr_mubi_e;

  typedef struct packed {
    logic main_pd_n;
    logic usb_clk_en_active;
    logic usb_clk_en_lp;
    logic io_clk_en;
    logic core_clk_en;
  } control_enables_t;

  typedef bit [pwrmgr_reg_pkg::NumWkups-1:0] wakeups_t;
  typedef bit [pwrmgr_reg_pkg::NumRstReqs-1:0] resets_t;

  // This is used to send all resets to rstmgr.
  typedef bit [pwrmgr_pkg::HwResetWidth-1:0] resets_out_t;

  // need a short name to avoid 100 line cut off
  parameter int MUBI4W = prim_mubi_pkg::MuBi4Width;

  // functions

  // variables
  bit [NUM_INTERRUPTS-1:0] exp_intr;
  wakeups_t exp_wakeup_reasons;
  control_enables_t control_enables;
  logic low_power_hint;

  // package sources
  `include "pwrmgr_env_cfg.sv"
  `include "pwrmgr_env_cov.sv"
  `include "pwrmgr_virtual_sequencer.sv"
  `include "pwrmgr_scoreboard.sv"
  `include "pwrmgr_env.sv"
  `include "pwrmgr_vseq_list.sv"

endpackage
