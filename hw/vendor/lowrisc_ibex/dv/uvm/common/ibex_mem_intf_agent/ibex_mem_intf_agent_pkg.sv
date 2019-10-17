// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "ibex_mem_intf.sv"

package ibex_mem_intf_agent_pkg;

  import uvm_pkg::*;
  import mem_model_pkg::*;

  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 32;

  typedef enum { READ, WRITE } rw_e;

  `include "uvm_macros.svh"
  `include "ibex_mem_intf_seq_item.sv"

  typedef uvm_sequencer#(ibex_mem_intf_seq_item) ibex_mem_intf_master_sequencer;

  `include "ibex_mem_intf_monitor.sv"
  `include "ibex_mem_intf_slave_driver.sv"
  `include "ibex_mem_intf_slave_sequencer.sv"
  `include "ibex_mem_intf_slave_seq_lib.sv"
  `include "ibex_mem_intf_slave_agent.sv"
  `include "ibex_mem_intf_master_driver.sv"
  `include "ibex_mem_intf_master_agent.sv"

endpackage
