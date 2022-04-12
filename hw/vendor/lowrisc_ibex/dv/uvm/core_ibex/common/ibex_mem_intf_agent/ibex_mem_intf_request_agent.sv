// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_request_agent
//------------------------------------------------------------------------------

class ibex_mem_intf_request_agent extends uvm_agent;

  ibex_mem_intf_request_driver driver;
  ibex_mem_intf_request_sequencer sequencer;
  ibex_mem_intf_monitor monitor;

  `uvm_component_utils(ibex_mem_intf_request_agent)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    monitor = ibex_mem_intf_monitor::type_id::create("monitor", this);
    if(get_is_active() == UVM_ACTIVE) begin
      driver = ibex_mem_intf_request_driver::type_id::create("driver", this);
      sequencer = ibex_mem_intf_request_sequencer::type_id::create("sequencer", this);
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if(get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction : connect_phase

endclass : ibex_mem_intf_request_agent
