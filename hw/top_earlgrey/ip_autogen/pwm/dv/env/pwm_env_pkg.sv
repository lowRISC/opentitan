// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwm_env_pkg;
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

  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // The DUT has a single alert signal.
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault"};

  // Constants.
  parameter bit [31:0] MAX_32 = 32'hFFFF_FFFF;
  parameter bit [15:0] MAX_16 = 16'hFFFF;
  parameter bit [26:0] MAX_27 = 27'h7FF_FFFF;

  // Duration of test in core clock cycles.
  parameter uint NUM_CYCLES = 'd1_049_000;

  // The DUT has a very flexible interface, clearly intended to support a wide range of bus and
  // core clock frequencies; however, large values of `CLK_DIV` are impractical in simulation.
  parameter bit [26:0] MAX_CLK_DIV = 15;

  // Phase counter configuration (CFG).
  typedef struct packed {
    bit [26:0]   ClkDiv;
    bit [3:0]    DcResn;
    bit          CntrEn;
  } cfg_reg_t;

  // Channel parameters (PWM_PARAM_i register).
  typedef struct packed {
    bit          BlinkEn;
    bit          HtbtEn;
    bit [15:0]   PhaseDelay;
  } param_reg_t;

  // Duty cycles (DUTY_CYCLE_i register).
  typedef struct packed {
    bit [15:0]   B;
    bit [15:0]   A;
  } duty_cycle_t;

  // Blink mode parameters (BLINK_PARAM_i register).
  typedef struct packed {
    bit [15:0]   Y;
    bit [15:0]   X;
  } blink_param_t;

  // The index of a multi-reg is given by the last character(s) of the name. The number of PWM
  // channels is parameterized.
  function automatic int unsigned get_multireg_idx(string name);
    int str_len = name.len();
    // Note: this extracts the final two characters which are either '_y' or 'xy',
    //       and because '_' is permitted in (System)Verilog numbers, it works for 0-99
    string index_str = name.substr(str_len-2, str_len-1);
    return index_str.atoi();
  endfunction

  // Package sources
  `include "pwm_env_cfg.sv"
  `include "pwm_env_cov.sv"
  `include "pwm_virtual_sequencer.sv"
  `include "pwm_scoreboard.sv"
  `include "pwm_env.sv"
  `include "pwm_vseq_list.sv"

endpackage : pwm_env_pkg
