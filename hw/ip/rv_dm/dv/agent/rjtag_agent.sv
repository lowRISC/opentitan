// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_agent extends uvm_agent;
  rjtag_driver    m_drv;
  rjtag_monitor   m_mon;
  rjtag_sequencer m_seqr;

  `uvm_component_utils(rjtag_agent)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (get_is_active() == UVM_ACTIVE) begin
      m_drv = rjtag_driver::type_id::create("m_drv", this);
      m_seqr = rjtag_sequencer::type_id::create("m_seqr", this);
    end

    m_mon = rjtag_monitor::type_id::create("m_mon", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE) begin
      m_drv.seq_item_port.connect(m_seqr.seq_item_export);
    end
  endfunction : connect_phase

endclass : rjtag_agent
