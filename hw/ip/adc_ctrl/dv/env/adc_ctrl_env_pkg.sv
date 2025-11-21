// Copyright lowRISC contributors (OpenTitan project).
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
  import push_pull_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault"};
  // Number of ADC channels
  parameter int unsigned ADC_CTRL_CHANNELS = ast_pkg::AdcChannels;
  // ADC data width
  parameter int ADC_CTRL_DATA_WIDTH = ast_pkg::AdcDataWidth;
  // Number of filters in the ADC Ctrl block
  parameter int unsigned ADC_CTRL_NUM_FILTERS = 8;
  // Interrupt index in interrupts interface
  parameter int ADC_CTRL_INTERRUPT_INDEX = 0;
  // Width of pwrup_width field
  parameter int ADC_CTRL_PWRUP_TIME_WIDTH = 4;
  // Width of wakeup field
  parameter int ADC_CTRL_WAKEUP_TIME_WIDTH = 24;
  // Width of adc_sample_ctl field
  parameter int ADC_CTRL_SAMPLE_CTL_WIDTH = 16;
  // Width of adc_lp_sample_ctl field
  parameter int ADC_CTRL_LP_SAMPLE_CTL_WIDTH = 4;

  // types

  //
  // ADC Push/pull types
  //
  // ADC Push Pull virtual interface type
  typedef virtual push_pull_if #(.DeviceDataWidth(ADC_CTRL_DATA_WIDTH)) adc_push_pull_vif_t;
  // ADC Push Pull agent type
  typedef push_pull_agent#(.DeviceDataWidth(ADC_CTRL_DATA_WIDTH)) adc_push_pull_agent_t;
  // ADC Push Pull config type
  typedef push_pull_agent_cfg#(.DeviceDataWidth(ADC_CTRL_DATA_WIDTH)) adc_push_pull_config_t;
  // ADC Push Pull item type
  typedef push_pull_item#(.DeviceDataWidth(ADC_CTRL_DATA_WIDTH)) adc_push_pull_item_t;
  // ADC Push Pull fifo type
  typedef uvm_tlm_analysis_fifo#(adc_push_pull_item_t) adc_push_pull_fifo_t;
  // Single ADC value
  typedef logic unsigned [ADC_CTRL_DATA_WIDTH - 1 : 0] adc_value_logic_t;
  typedef bit unsigned [ADC_CTRL_DATA_WIDTH - 1 : 0] adc_value_t;
  // Wakeup virtual interface
  typedef virtual pins_if #(1) wakeup_vif_t;

  // Type of test we are executing
  typedef enum bit [1:0] {
    AdcCtrlTestmodeOneShot,
    AdcCtrlTestmodeNormal,
    AdcCtrlTestmodeLowpower
  } adc_ctrl_testmode_e;

  // Reset to generate
  typedef enum bit {
    AdcCtrlResetModeFsm,
    AdcCtrlResetModeHw
  } adc_ctrl_reset_mode_e;

  typedef class adc_ctrl_filter_cfg;

  // Constants
  // Filter defaults - applies to all channels
  const adc_ctrl_filter_cfg FILTER_CFG_DEFAULTS[] = '{
      adc_ctrl_filter_cfg::make("default0", 149, 279, 1),
      adc_ctrl_filter_cfg::make("default1", 391, 524, 1),
      adc_ctrl_filter_cfg::make("default2", 712, 931, 1),
      adc_ctrl_filter_cfg::make("default3", 712, 847, 1),
      adc_ctrl_filter_cfg::make("default4", 349, 512, 1),
      adc_ctrl_filter_cfg::make("default5", 405, 503, 1),
      adc_ctrl_filter_cfg::make("default6", 186, 279, 1),
      adc_ctrl_filter_cfg::make("default7", 116, 954, 0)
  };

  // package sources
  `include "adc_ctrl_env_cfg.sv"
  `include "adc_ctrl_env_var_filter_cfg.sv"
  `include "adc_ctrl_filter_cfg.sv"
  `include "adc_ctrl_env_cov.sv"
  `include "adc_ctrl_virtual_sequencer.sv"
  `include "adc_ctrl_scoreboard.sv"
  `include "adc_ctrl_env.sv"
  `include "adc_ctrl_vseq_list.sv"

endpackage
