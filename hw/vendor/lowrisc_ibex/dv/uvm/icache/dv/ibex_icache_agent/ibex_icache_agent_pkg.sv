// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // local types
  // forward declare classes to allow typedefs below
  typedef class ibex_icache_item;
  typedef class ibex_icache_agent_cfg;

  // reuse dv_base_seqeuencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(ibex_icache_item),
                              .CFG_T (ibex_icache_agent_cfg)) ibex_icache_sequencer;

  // functions

  // package sources
  `include "ibex_icache_item.sv"
  `include "ibex_icache_agent_cfg.sv"
  `include "ibex_icache_agent_cov.sv"
  `include "ibex_icache_driver.sv"
  `include "ibex_icache_monitor.sv"
  `include "ibex_icache_agent.sv"
  `include "ibex_icache_seq_list.sv"

endpackage: ibex_icache_agent_pkg
