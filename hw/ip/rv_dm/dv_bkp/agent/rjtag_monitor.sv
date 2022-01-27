// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_monitor extends uvm_monitor;

  virtual jtag_if vif;

  uvm_analysis_port #(rjtag_seq_item) item_collected_port;

  rjtag_seq_item trans_collected;

  `uvm_component_utils(rjtag_monitor)

  function new (string name, uvm_component parent);
    super.new(name, parent);
    trans_collected = new();
    item_collected_port = new("item_collected_port", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual jtag_if)::get(this,"","vif",vif)) begin
      `uvm_fatal("NO_VIF", {"virtual interface must be set for:",
        get_full_name(),".vif"});
    end
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    item_collected_port.write(trans_collected);
  endtask : run_phase

endclass : rjtag_monitor
