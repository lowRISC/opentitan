// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import ibex_icache_core_agent_pkg::*;
  import ibex_mem_intf_agent_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types
  typedef dv_base_reg_block ibex_icache_reg_block;

  // functions

  // package sources
  `include "ibex_icache_env_cfg.sv"
  `include "ibex_icache_env_cov.sv"
  `include "ibex_icache_virtual_sequencer.sv"
  `include "ibex_icache_scoreboard.sv"
  `include "ibex_icache_env.sv"
  `include "ibex_icache_vseq_list.sv"

endpackage
