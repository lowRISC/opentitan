// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_agent extends uvm_agent;
  `uvm_component_utils(reset_agent)

  // An analysis port that broadcasts resets
  uvm_analysis_port #(reset_edge_item) m_analysis_port;

  // The virtual interface that is tracked. This can either be set by calling set_vif() before the
  // build phase, or provided through uvm_config_db.
  local virtual clk_rst_if m_vif;

  // The monitor for the interface
  local reset_monitor m_monitor;

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);

  // Set m_vif to the provided interface
  extern function void set_vif(virtual clk_rst_if vif);

  // Get a handle to a uvm_event that is triggered on every edge of the reset line. The data value
  // that comes with the event is a reset_edge_item (the item that is also broadcast through
  // m_analysis_port).
  extern function uvm_event get_event();
endclass

function reset_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void reset_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  m_analysis_port = new("m_analysis_port", this);

  if (m_vif == null && !uvm_config_db#(virtual clk_rst_if)::get(this, "", "vif", m_vif)) begin
    `uvm_fatal(get_full_name(), "failed to get vif from uvm_config_db")
  end
  if (m_vif == null) begin
    `uvm_fatal(get_full_name(), "No non-null m_vif provided.")
  end

  m_monitor = reset_monitor::type_id::create("m_monitor", this);
  m_monitor.set_vif(m_vif);
endfunction

function void reset_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  m_monitor.m_analysis_port.connect(m_analysis_port);
endfunction

function void reset_agent::set_vif(virtual clk_rst_if vif);
  if (m_vif != null) `uvm_fatal(get_full_name(), "Cannot set vif: m_vif is already non-null.")
  m_vif = vif;
endfunction

function uvm_event reset_agent::get_event();
  if (m_monitor == null) `uvm_fatal(get_full_name(), "Cannot get event before monitor constructed.")
  return m_monitor.get_event();
endfunction
