// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package gpio_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // no. of gpio pins
  parameter NUM_GPIOS     = 32;
  // no. of cycles for noise filter
  parameter FILTER_CYCLES = 16;

  typedef virtual pins_if #(NUM_GPIOS) gpio_vif;
  typedef class gpio_env_cfg;
  typedef class gpio_env_cov;
  typedef cip_base_virtual_sequencer #(gpio_env_cfg, gpio_env_cov) gpio_virtual_sequencer;

  // structure to indicate gpio pin transition and type of transition
  // transition: 1-yes, 0-no
  // rose_or_fell: 1-rising edge transition, 0-falling edge transition
  typedef struct packed { bit transition; bit rose_or_fell; } gpio_transition;

  // structure to indicate whether or not register update is due for particular gpio register
  // need_update: 1-update is due, 0-update is not due
  // reg_value: value to be updated when update is due
  typedef struct packed { bit need_update; bit [TL_DW-1:0] reg_value; } gpio_reg_update_due;
  // functions

  // package sources
  `include "gpio_reg_block.sv"
  `include "gpio_env_cfg.sv"
  `include "gpio_env_cov.sv"
  `include "gpio_scoreboard.sv"
  `include "gpio_env.sv"
  `include "gpio_vseq_list.sv"
endpackage
