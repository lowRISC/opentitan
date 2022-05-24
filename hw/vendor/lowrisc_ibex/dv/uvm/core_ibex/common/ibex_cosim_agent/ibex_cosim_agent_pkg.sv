// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_cosim_agent_pkg;
`ifdef INC_IBEX_COSIM
  import uvm_pkg::*;
  import ibex_mem_intf_agent_pkg::*;

  `include "uvm_macros.svh"

  `include "ibex_cosim_cfg.sv"
  `include "ibex_rvfi_seq_item.sv"
  `include "ibex_rvfi_monitor.sv"
  `include "ibex_ifetch_seq_item.sv"
  `include "ibex_ifetch_monitor.sv"
  `include "ibex_ifetch_pmp_seq_item.sv"
  `include "ibex_ifetch_pmp_monitor.sv"
  `include "ibex_cosim_scoreboard.sv"
  `include "ibex_cosim_agent.sv"
`endif
endpackage
