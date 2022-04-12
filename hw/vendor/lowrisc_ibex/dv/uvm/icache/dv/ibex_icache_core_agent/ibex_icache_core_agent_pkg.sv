// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_core_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  typedef enum {
    ICacheCoreTransTypeBranch,
    ICacheCoreTransTypeReq
  } ibex_icache_core_trans_type_e;

  typedef enum {
    ICacheCoreBusTransTypeBranch,
    ICacheCoreBusTransTypeFetch,
    ICacheCoreBusTransTypeInvalidate,
    ICacheCoreBusTransTypeEnable,
    ICacheCoreBusTransTypeBusy
  } ibex_icache_core_bus_trans_type_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package sources
  `include "ibex_icache_core_req_item.sv"
  `include "ibex_icache_core_rsp_item.sv"
  `include "ibex_icache_core_bus_item.sv"
  `include "ibex_icache_core_agent_cfg.sv"
  `include "ibex_icache_core_agent_cov.sv"
  `include "ibex_icache_core_sequencer.sv"
  `include "ibex_icache_core_driver.sv"
  `include "ibex_icache_core_monitor.sv"
  `include "ibex_icache_core_agent.sv"
  `include "ibex_icache_core_seq_list.sv"

endpackage: ibex_icache_core_agent_pkg
