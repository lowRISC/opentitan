// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import bus_params_pkg::*;
  import dv_utils_pkg::*;
  import ibex_icache_core_agent_pkg::*;
  import ibex_icache_mem_agent_pkg::*;
  import push_pull_agent_pkg::*;
  import dv_lib_pkg::*;
  import ibex_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types

  // functions

  typedef push_pull_agent#(.DeviceDataWidth(194)) scrambling_key_agent;
  typedef push_pull_agent_cfg#(.DeviceDataWidth(194)) scrambling_key_agent_cfg;
  typedef virtual push_pull_if#(.DeviceDataWidth(194)) scrambling_key_vif;
  typedef virtual ibex_icache_ram_if#(.TagSizeECC(IC_TAG_SIZE + 6),
                                      .LineSizeECC(IC_LINE_BEATS * (BUS_SIZE + 7))
  ) ibex_icache_ram_vif;

  // package sources
  `include "ibex_icache_env_cfg.sv"
  `include "ibex_icache_env_cov.sv"
  `include "ibex_icache_virtual_sequencer.sv"
  `include "ibex_icache_scoreboard.sv"
  `include "ibex_icache_env.sv"
  `include "ibex_icache_vseq_list.sv"

endpackage
