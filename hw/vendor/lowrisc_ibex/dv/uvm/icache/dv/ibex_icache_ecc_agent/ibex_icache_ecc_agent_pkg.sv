// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_ecc_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef class ibex_icache_ecc_item;
  typedef class ibex_icache_ecc_agent_cfg;

  typedef dv_base_sequencer #(.ITEM_T(ibex_icache_ecc_item),
                              .CFG_T (ibex_icache_ecc_agent_cfg)) ibex_icache_ecc_sequencer;

  // package sources
  `include "ibex_icache_ecc_item.sv"
  `include "ibex_icache_ecc_bus_item.sv"
  `include "ibex_icache_ecc_agent_cfg.sv"
  `include "ibex_icache_ecc_driver.sv"
  `include "ibex_icache_ecc_monitor.sv"
  `include "ibex_icache_ecc_agent.sv"
  `include "ibex_icache_ecc_seq_list.sv"

endpackage: ibex_icache_ecc_agent_pkg
