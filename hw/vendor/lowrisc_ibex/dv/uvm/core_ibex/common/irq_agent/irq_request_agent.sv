// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class irq_request_agent extends uvm_agent;

  irq_request_driver     driver;
  irq_request_sequencer  sequencer;
  irq_monitor         monitor;

  `uvm_component_utils(irq_request_agent)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    monitor = irq_monitor::type_id::create("monitor", this);
    if (get_is_active() == UVM_ACTIVE) begin
      driver = irq_request_driver::type_id::create("driver", this);
      sequencer = irq_request_sequencer::type_id::create("sequencer", this);
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction : connect_phase

endclass : irq_request_agent
