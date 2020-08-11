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
  import spi_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import chip_ral_pkg::*;
  import sw_test_status_pkg::*;
  import xbar_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  parameter uint NUM_GPIOS = 16;

  // SW constants
  parameter bit [TL_AW-1:0] SW_DV_LOG_ADDR = 32'h1000fffc;
  parameter bit [TL_AW-1:0] SW_DV_TEST_STATUS_ADDR = 32'h1000fff8;

  typedef virtual pins_if #(NUM_GPIOS) gpio_vif;
  typedef virtual mem_bkdr_if mem_bkdr_vif;
  typedef virtual sw_logger_if sw_logger_vif;

  // Types of memories in the chip.
  typedef enum {
    Rom,
    Ram,
    FlashBank0,
    FlashBank1,
    SpiMem
  } chip_mem_e;

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
