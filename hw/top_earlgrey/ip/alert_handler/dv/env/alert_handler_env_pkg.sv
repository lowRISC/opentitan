// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package alert_handler_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import alert_esc_agent_pkg::*;
  import dv_base_reg_pkg::*;
  import cip_base_pkg::*;
  import alert_handler_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_ALERTS                  = alert_handler_reg_pkg::NAlerts;
  parameter uint NUM_ESCS                    = 4;
  parameter uint NUM_MAX_ESC_SEV             = 8;
  parameter uint NUM_ESC_SIGNALS             = 4;
  parameter uint NUM_ALERT_HANDLER_CLASSES   = 4;
  parameter uint NUM_ESC_PHASES              = 4;
  parameter uint NUM_ALERT_HANDLER_CLASS_MSB = $clog2(NUM_ALERT_HANDLER_CLASSES) - 1;
  parameter uint MIN_CYCLE_PER_PHASE         = 2;
  parameter uint NUM_LOCAL_ALERT             = 4;
  parameter bit  [NUM_ALERTS-1:0] ASYNC_ON   = alert_handler_reg_pkg::AsyncOn;
  // ignore esc signal cycle count after ping occurs - as ping response might ended up adding one
  // extra cycle to the calculated cnt, or even combine two signals into one.
  parameter uint IGNORE_CNT_CHECK_NS         = 100_000_000;
  // set the max ping timeout cycle to constrain the simulation run time
  parameter uint MAX_PING_TIMEOUT_CYCLE     = 100;
  // types
  typedef enum {
    EscPhase0,
    EscPhase1,
    EscPhase2,
    EscPhase3
  } esc_phase_e;

  typedef enum {
    AlertClassCtrlEn,
    AlertClassCtrlLock,
    AlertClassCtrlEnE0,
    AlertClassCtrlEnE1,
    AlertClassCtrlEnE2,
    AlertClassCtrlEnE3,
    AlertClassCtrlMapE0,
    AlertClassCtrlMapE1,
    AlertClassCtrlMapE2,
    AlertClassCtrlMapE3
  } alert_class_ctrl_e;

  typedef enum {
    EscStateIdle     = 'b000,
    EscStateTimeout  = 'b001,
    EscStateTerminal = 'b011,
    EscStatePhase0   = 'b100,
    EscStatePhase1   = 'b101,
    EscStatePhase2   = 'b110,
    EscStatePhase3   = 'b111
  } esc_state_e;

  typedef enum {
    LocalAlertPingFail,
    LocalEscPingFail,
    LocalAlertIntFail,
    LocalEscIntFail
  } local_alert_type_e;

  // forward declare classes to allow typedefs below
  typedef virtual pins_if #(NUM_MAX_ESC_SEV) esc_en_vif;
  typedef virtual pins_if #(1) entropy_vif;

  // functions

  // package sources
  `include "alert_handler_env_cfg.sv"
  `include "alert_handler_env_cov.sv"
  `include "alert_handler_virtual_sequencer.sv"
  `include "alert_handler_scoreboard.sv"
  `include "alert_handler_env.sv"
  `include "alert_handler_vseq_list.sv"

endpackage
