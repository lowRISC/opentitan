// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_response_sequencer
//------------------------------------------------------------------------------

class ibex_mem_intf_response_sequencer extends uvm_sequencer #(ibex_mem_intf_seq_item);

  // TLM port to peek the address phase from the response monitor
  uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item) addr_ph_port;
  uvm_analysis_imp #(int, ibex_mem_intf_response_sequencer) outstanding_accesses_imp;
  ibex_mem_intf_response_agent_cfg cfg;

  event monitor_tick = null;
  int outstanding_accesses = 0;

  `uvm_component_utils(ibex_mem_intf_response_sequencer)

  function new (string name, uvm_component parent);
    super.new(name, parent);
    addr_ph_port = new("addr_ph_port_sequencer", this);
    outstanding_accesses_imp = new("outstanding_access_imp", this);
  endfunction : new

  // On reset, empty the tlm fifo
  function void reset();
    addr_ph_port.flush();
  endfunction

  function void write(int x);
    outstanding_accesses = x;
  endfunction

endclass : ibex_mem_intf_response_sequencer
