// Copyright lowRISC contributors.
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

  import alert_pkg::alert_crashdump_t;
  import rv_core_ibex_pkg::cpu_crash_dump_t;

  import sec_cm_pkg::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"fatal_fault", "fatal_cnsty_fault"};
  parameter uint NUM_ALERTS = 2;

  // Sorted instances of rstmgr_leaf_rst modules in top_earlgrey's rstmgr.
  // This can be generated from the source using
  //   grep -A 5 rstmgr_leaf_rst <path to rstmgr.sv> | \
  //     egrep '^[ ]+\) u_' | sed 's/[ )(]//g' | sort | \
  //     sed 's/\(.*\)/    \"\1\",/'
  parameter string LIST_OF_LEAFS[] = {
    "u_d0_i2c0",
    "u_d0_i2c1",
    "u_d0_i2c2",
    "u_d0_lc",
    "u_d0_lc_io",
    "u_d0_lc_io_div2",
    // There are 4 rstmgr_leaf_rst instances with security checks disabled.
    // "u_d0_lc_io_div4",
    // "u_d0_lc_io_div4_shadowed",
    "u_d0_lc_usb",
    "u_d0_spi_device",
    "u_d0_spi_host0",
    "u_d0_spi_host1",
    "u_d0_sys",
    "u_d0_usb",
    "u_d0_usb_aon",
    "u_daon_lc",
    "u_daon_lc_aon",
    "u_daon_lc_io",
    "u_daon_lc_io_div2",
    // Same as comment above.
    // "u_daon_lc_io_div4",
    // "u_daon_lc_io_div4_shadowed",
    "u_daon_lc_shadowed",
    "u_daon_lc_usb",
    "u_daon_por",
    "u_daon_por_io",
    "u_daon_por_io_div2",
    "u_daon_por_io_div4",
    "u_daon_por_usb",
    "u_daon_sys_io_div4"
  };

  // Instances of rstmgr_leaf_rst modules which have a shadow pair.
  parameter string LIST_OF_SHADOW_LEAFS[] = {
    "u_d0_lc_io_div4",
    "u_daon_lc",
    "u_daon_lc_io_div4"
  };

  // types
  typedef logic [NumSwResets-1:0] sw_rst_t;
  typedef class rstmgr_scoreboard;

  typedef logic [$bits(alert_crashdump_t)-1:0] linearized_alert_dump_t;

  // functions

  // package sources
  `include "rstmgr_env_cfg.sv"
  `include "rstmgr_env_cov.sv"
  `include "rstmgr_virtual_sequencer.sv"
  `include "rstmgr_scoreboard.sv"
  `include "rstmgr_env.sv"
  `include "rstmgr_vseq_list.sv"

endpackage
