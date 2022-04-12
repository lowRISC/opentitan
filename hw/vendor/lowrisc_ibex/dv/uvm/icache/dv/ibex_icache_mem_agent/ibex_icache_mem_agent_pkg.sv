// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_mem_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package sources
  `include "ibex_icache_mem_req_item.sv"
  `include "ibex_icache_mem_resp_item.sv"
  `include "ibex_icache_mem_bus_item.sv"
  `include "ibex_icache_mem_model.sv"
  `include "ibex_icache_mem_agent_cfg.sv"
  `include "ibex_icache_mem_agent_cov.sv"
  `include "ibex_icache_mem_driver.sv"
  `include "ibex_icache_mem_monitor.sv"
  `include "ibex_icache_mem_sequencer.sv"
  `include "ibex_icache_mem_agent.sv"
  `include "ibex_icache_mem_seq_list.sv"

endpackage: ibex_icache_mem_agent_pkg
