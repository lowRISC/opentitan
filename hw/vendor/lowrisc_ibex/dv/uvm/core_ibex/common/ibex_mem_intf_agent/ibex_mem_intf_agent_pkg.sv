// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_mem_intf_agent_pkg;

  import uvm_pkg::*;
  import ibex_mem_intf_pkg::*;
  import mem_model_pkg::*;
  import ibex_cosim_agent_pkg::*;

  `include "uvm_macros.svh"

  typedef uvm_sequencer#(ibex_mem_intf_seq_item) ibex_mem_intf_request_sequencer;

  `include "ibex_mem_intf_monitor.sv"
  `include "ibex_mem_intf_response_agent_cfg.sv"
  `include "ibex_mem_intf_response_driver.sv"
  `include "ibex_mem_intf_response_sequencer.sv"
  `include "ibex_mem_intf_response_seq_lib.sv"
  `include "ibex_mem_intf_response_agent.sv"
  `include "ibex_mem_intf_request_driver.sv"
  `include "ibex_mem_intf_request_agent.sv"

endpackage
