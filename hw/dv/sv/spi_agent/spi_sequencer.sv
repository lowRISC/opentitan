// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_sequencer extends dv_base_sequencer#(spi_item, spi_agent_cfg, spi_item);
  `uvm_component_utils(spi_sequencer)

  // Analysis imp to receive items from host AP in monitor
  uvm_analysis_imp#(spi_item, spi_sequencer) host_mon_analysis_imp;

  // Holds up to 1 item at a time sent by the monitor
  spi_item host_mon_item_q[$];

  function new(string name, uvm_component parent);
    super.new(name, parent);
    host_mon_analysis_imp = new("mon_analysis_imp", this);
  endfunction : new

  virtual function void write(spi_item item);
    `uvm_info(`gfn, $sformatf("Received host item from monitor: \n%0s", item.sprint), UVM_DEBUG)
    // Clear the queue then push the item
    host_mon_item_q = {};
    host_mon_item_q.push_back(item);
  endfunction

endclass : spi_sequencer
