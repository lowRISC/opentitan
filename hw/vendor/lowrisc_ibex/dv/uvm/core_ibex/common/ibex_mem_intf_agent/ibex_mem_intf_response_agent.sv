// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_response_agent
//------------------------------------------------------------------------------

class ibex_mem_intf_response_agent extends uvm_agent;

  ibex_mem_intf_response_driver     driver;
  ibex_mem_intf_response_sequencer  sequencer;
  ibex_mem_intf_monitor             monitor;
  ibex_mem_intf_response_agent_cfg  cfg;

  `uvm_component_utils(ibex_mem_intf_response_agent)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    monitor = ibex_mem_intf_monitor::type_id::create("monitor", this);
    cfg = ibex_mem_intf_response_agent_cfg::type_id::create("cfg", this);
    if(get_is_active() == UVM_ACTIVE) begin
      driver = ibex_mem_intf_response_driver::type_id::create("driver", this);
      sequencer = ibex_mem_intf_response_sequencer::type_id::create("sequencer", this);
    end
    if(!uvm_config_db#(virtual ibex_mem_intf)::get(this, "", "vif", cfg.vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if(get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
      monitor.addr_ph_port.connect(sequencer.addr_ph_port.analysis_export);
    end
    driver.cfg = cfg;
    sequencer.cfg = cfg;
  endfunction : connect_phase

  function void reset();
    sequencer.reset();
  endfunction

endclass : ibex_mem_intf_response_agent
