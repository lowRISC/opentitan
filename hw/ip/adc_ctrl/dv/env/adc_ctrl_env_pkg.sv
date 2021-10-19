// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package adc_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import adc_ctrl_ral_pkg::*;
  import ast_adc_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // Number of ADC channels
  parameter AdcCtrlChannels =2;

  // Number of filters in the ADC Ctrl block
  parameter AdcCtrlFilters = 8;

  // types
  // Type of test we are executing
  typedef enum {
    AdcCtrlOnehot, 
    AdcCtrlNormal,
    AdcCtrlLowpower
  } adc_ctrl_testmode_e;

  // Filter condition coding
  typedef enum bit {
    AdcCtrlOut = 0,
    AdcCtrlIn  = 1
  } adc_ctrl_filter_cond_e;

  // Filter configurration
  typedef struct packed {
    adc_ctrl_filter_cond_e cond; // Condition
    int min_v; // Minimum value
    int max_v; // Maximum value
    bit en;  // Enable
  } adc_ctrl_filter_cfg_t;

  // Constants
  // Filter defaults - applies to all channels
  const adc_ctrl_filter_cfg_t FilterCfgDefaults[] = '{
      '{min_v: 149, max_v: 279, cond: AdcCtrlIn, en: 1},
      '{min_v: 391, max_v: 524, cond: AdcCtrlIn, en: 1},
      '{min_v: 712, max_v: 931, cond: AdcCtrlIn, en: 1},
      '{min_v: 712, max_v: 847, cond: AdcCtrlIn, en: 1},
      '{min_v: 349, max_v: 512, cond: AdcCtrlIn, en: 1},
      '{min_v: 405, max_v: 503, cond: AdcCtrlIn, en: 1},
      '{min_v: 186, max_v: 279, cond: AdcCtrlIn, en: 1},
      '{min_v: 116, max_v: 954, cond: AdcCtrlOut, en: 1}
      };
  // functions and tasks
 

  // package sources
  `include "adc_ctrl_env_cfg.sv"
  `include "adc_ctrl_env_cov.sv"
  `include "adc_ctrl_virtual_sequencer.sv"
  `include "adc_ctrl_scoreboard.sv"
  `include "adc_ctrl_env.sv"
  `include "adc_ctrl_vseq_list.sv"

endpackage
