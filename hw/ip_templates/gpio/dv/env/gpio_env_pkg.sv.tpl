// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${module_instance_name}_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import ${module_instance_name}_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // no. of ${module_instance_name} pins
  parameter uint NUM_GPIOS     = 32;
  // no. of cycles for noise filter
  parameter uint FILTER_CYCLES = 16;
  // No. of alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};
  // No. of input period counters
  parameter uint NUM_INP_PRD_CNT = ${num_inp_period_counters};

  typedef virtual pins_if #(NUM_GPIOS) ${module_instance_name}_vif;
  typedef virtual ${module_instance_name}_straps_if straps_vif;
  typedef class ${module_instance_name}_env_cfg;
  typedef class ${module_instance_name}_env_cov;
  typedef class ${module_instance_name}_seq_item;
  typedef class ${module_instance_name}_strap_agent_cfg;

  // structure to indicate ${module_instance_name} pin transition and type of transition
  // transition_occurred: 1-yes, 0-no
  // is_rising_edge: 1-rising edge transition, 0-falling edge transition
  typedef struct packed {
    bit transition_occurred;
    bit is_rising_edge;
  } ${module_instance_name}_transition_t;

  // structure to indicate whether or not register update is due for particular ${module_instance_name} register
  // needs_update: 1-update is due, 0-update is not due
  // reg_value: value to be updated when update is due
  // eval_time: time stamp of event, which triggered interrupt update
  typedef struct packed {
    bit needs_update;
    bit [TL_DW-1:0] reg_value;
    time eval_time;
  } ${module_instance_name}_reg_update_due_t;

  // package sources
  `include "${module_instance_name}_agent/${module_instance_name}_strap_agent_cfg.sv"
  `include "${module_instance_name}_agent/${module_instance_name}_data_agent_cfg.sv"
  `include "${module_instance_name}_env_cfg.sv"
  `include "seq_lib/${module_instance_name}_seq_item.sv"
  `include "${module_instance_name}_virtual_sequencer.sv"

  typedef ${module_instance_name}_virtual_sequencer #(.CFG_T(gpio_strap_agent_cfg),
    .COV_T(${module_instance_name}_env_cov),
    .ITEM_T(uvm_sequence_item),
    .RSP_ITEM_T(uvm_sequence_item)) strap_sequencer;

  `include "${module_instance_name}_agent/${module_instance_name}_strap_monitor.sv"
  `include "${module_instance_name}_agent/${module_instance_name}_strap_driver.sv"
  `include "${module_instance_name}_agent/${module_instance_name}_strap_agent.sv"
  `include "gpio_agent/gpio_data_driver.sv"
  `include "gpio_agent/gpio_data_monitor.sv"
  `include "gpio_agent/gpio_data_agent.sv"
  `include "model/gpio_model.sv"
  `include "${module_instance_name}_env_cov.sv"
  `include "${module_instance_name}_vseq_list.sv"
  `include "${module_instance_name}_scoreboard.sv"
  `include "${module_instance_name}_env.sv"
endpackage
