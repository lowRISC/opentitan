// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package chip_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import uart_agent_pkg::*;
  import jtag_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import chip_ral_pkg::*;

  // import individual env IP env pkgs
  import uart_env_pkg::*;
  import gpio_env_pkg::*;
  import hmac_env_pkg::*;
  import rv_timer_env_pkg::*;
  import spi_device_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  parameter         NUM_GPIOS   = 16;

  typedef virtual pins_if #(NUM_GPIOS)  gpio_vif;
  typedef virtual mem_bkdr_if           mem_bkdr_vif;
  typedef virtual sw_msg_monitor_if     sw_msg_monitor_vif;

  // enum to indicate cpu test pass / fail status
  typedef enum bit [15:0] {
    CpuUnderReset   = 16'hffff,   // cpu is held under reset
    CpuTestRunning  = 16'hb004,   // cpu test running
    CpuTestPass     = 16'hff00,   // cpu test passed
    CpuTestFail     = 16'h00ff    // cpu test failed
  } cpu_test_state_e;

  typedef enum {
    Rom,
    Ram,
    FlashBank0,
    FlashBank1,
    SpiMem
  } chip_mem_e;

  typedef class chip_tl_seq_item;
  typedef tl_reg_adapter #(.ITEM_T(chip_tl_seq_item)) chip_tl_reg_adapter;

  // functions

  // package sources
  `include "chip_tl_seq_item.sv"
  `include "chip_env_cfg.sv"
  `include "chip_env_cov.sv"
  `include "chip_virtual_sequencer.sv"
  `include "chip_scoreboard.sv"
  `include "chip_env.sv"
  `include "chip_vseq_list.sv"
endpackage
