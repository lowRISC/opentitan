// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "irq_if.sv"

package irq_agent_pkg;

  import uvm_pkg::*;

  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 32;

  `include "uvm_macros.svh"
  `include "irq_seq_item.sv"

  typedef uvm_sequencer#(irq_seq_item) irq_master_sequencer;

  `include "irq_monitor.sv"
  `include "irq_master_driver.sv"
  `include "irq_master_agent.sv"

endpackage
