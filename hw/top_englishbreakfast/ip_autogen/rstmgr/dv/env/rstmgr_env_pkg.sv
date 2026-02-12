// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rstmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rstmgr_ral_pkg::*;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  import rstmgr_reg_pkg::NumHwResets;
  import rstmgr_reg_pkg::NumSwResets;

  import alert_handler_pkg::alert_crashdump_t;
  import rv_core_ibex_pkg::cpu_crash_dump_t;

  import sec_cm_pkg::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault", "fatal_cnsty_fault"};

  // Sorted instances of rstmgr_leaf_rst instances with security checks enabled.
  parameter string LIST_OF_LEAFS[] = {
    "u_d0_lc",
    "u_d0_lc_shadowed",
    "u_d0_spi_device",
    "u_d0_spi_host0",
    "u_d0_sys",
    "u_d0_sys_aon",
    "u_d0_sys_io_div4",
    "u_d0_sys_shadowed",
    "u_d0_usb",
    "u_daon_por",
    "u_daon_por_io",
    "u_daon_por_io_div2",
    "u_daon_por_io_div4",
    "u_daon_por_io_div4_shadowed",
    "u_daon_por_usb",
    "u_daon_sys_aon",
    "u_daon_sys_io_div4"
  };

  // Instances of rstmgr_leaf_rst modules which have a shadow pair.
  parameter string LIST_OF_SHADOW_LEAFS[] = {
    "u_d0_lc",
    "u_d0_sys",
    "u_daon_por_io_div4"
  };

  // types
  typedef logic [NumSwResets-1:0] sw_rst_t;
  typedef class rstmgr_scoreboard;

  typedef logic [$bits(alert_crashdump_t)-1:0] linearized_alert_dump_t;

  // This is used to capture the values of CSR fields are reset by POR only, so these CSR
  // values can be restored to their pre-reset value right after a reset is done and undo
  // the dv_base reset clearing them.
  typedef struct packed {
    logic       alert_info_ctrl_en;
    logic [3:0] alert_info_ctrl_index;
    logic       cpu_info_ctrl_en;
    logic [3:0] cpu_info_ctrl_index;
  } rstmgr_values_of_por_csr_fields_t;

  // functions

  // package sources
  `include "rstmgr_env_cfg.sv"
  `include "rstmgr_env_cov.sv"
  `include "rstmgr_virtual_sequencer.sv"
  `include "rstmgr_scoreboard.sv"
  `include "rstmgr_env.sv"
  `include "rstmgr_vseq_list.sv"

endpackage
