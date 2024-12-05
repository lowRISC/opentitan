// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwm_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import pwm_monitor_pkg::*;
  import pwm_reg_pkg::*;
  import pwm_ral_pkg::*;

  parameter uint PWM_NUM_CHANNELS = pwm_reg_pkg::NOutputs;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};
  parameter bit [31:0] MAX_32 = 32'hFFFF_FFFF;
  parameter bit [15:0] MAX_16 = 16'hFFFF;
  parameter bit [26:0] MAX_27 = 27'h7FF_FFFF;
  parameter uint NUM_CYCLES = 'd1_049_000;
  parameter bit [26:0] MAX_CLK_DIV = 15;

  // datatype
  typedef enum bit {
    Enable  = 1'b1,
    Disable = 1'b0
  } pwm_status_e;

  typedef struct packed {
    bit [26:0]   ClkDiv;
    bit [3:0]    DcResn;
    bit          CntrEn;
  } cfg_reg_t;

  typedef struct packed {
    bit          BlinkEn;
    bit          HtbtEn;
    bit [15:0]   PhaseDelay;
  } param_reg_t;

  typedef struct packed {
    bit [15:0]   B;
    bit [15:0]   A;
  } dc_blink_t;

  // the index of multi-reg is at the last char of the name
  function automatic int get_multireg_idx(string name);
    string s = name.getc(name.len - 1);
    return s.atoi();
  endfunction

  // package sources
  `include "pwm_seq_cfg.sv"
  `include "pwm_env_cfg.sv"
  `include "pwm_env_cov.sv"
  `include "pwm_virtual_sequencer.sv"
  `include "pwm_scoreboard.sv"
  `include "pwm_env.sv"
  `include "pwm_vseq_list.sv"

endpackage : pwm_env_pkg
