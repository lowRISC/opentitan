// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A monitor that watches a reset_if.

class reset_monitor extends uvm_monitor;
  `uvm_component_utils(reset_monitor)

  // The interface being tracked. Set this with set_vif().
  local virtual clk_rst_if m_vif;

  // An event that is triggered on every edge of the reset line. Get this with get_event().
  local uvm_event m_event;

  // The analysis port for observed resets.
  uvm_analysis_port #(reset_edge_item) m_analysis_port;

  extern function new(string name, uvm_component parent);
  extern function void build_phase (uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  // Set the interface that is being tracked
  extern function void set_vif(virtual clk_rst_if vif);

  // Get a handle to a uvm_event that is triggered on every edge of the reset line. The data value
  // that comes with the event a reset_edge_item that represents the new value of the reset line.
  extern function uvm_event get_event();

  // Track requests and responses on m_vif
  //
  // This tracks the m_vif.rst_n signal, which has type logic (4-state). Unknown values (x and z)
  // are ignored, so there is only an edge when transitioning between the known values. For example,
  // the sequence ... 0, x, 0, ... does not contain a transition and the sequence ... 0, x, 1, ...
  // contains a transition as rst_n changes to 1.
  extern local task watch_interface();
endclass

function reset_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
  m_event = new("m_event");
endfunction

function void reset_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  m_analysis_port = new("m_analysis_port", this);

  if (m_vif == null && !uvm_config_db#(virtual clk_rst_if)::get(this, "", "vif", m_vif)) begin
    `uvm_fatal(get_full_name(), "Interface neither supplied with set_vif nor with uvm_config_db.")
  end
  if (m_vif == null) `uvm_fatal(get_full_name(), "vif from uvm_config_db was null.")
endfunction

task reset_monitor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    watch_interface();
  join
endtask

function void reset_monitor::set_vif(virtual clk_rst_if vif);
  m_vif = vif;
endfunction

function uvm_event reset_monitor::get_event();
  return m_event;
endfunction

task reset_monitor::watch_interface();
  // We're only interested in known states, so start by waiting for the state to become 0 or 1.
  wait (!$isunknown(m_vif.rst_n));

  forever begin
    reset_edge_item item;

    // cur_val is a bit holding the current state (which will indeed be a bit at this point because
    // of the logic in the rest of this task).
    bit cur_val = m_vif.rst_n;

    // Generate an item that reports our arrival at the state with rst_n equal to cur_val.
    item = reset_edge_item::type_id::create("item");
    item.m_new_state = cur_val;

    // Write that item to the analysis port (for consumption by components) and trigger the event
    // with the item attached. The latter can be monitored by other objects, like sequences, too.
    m_analysis_port.write(item);
    m_event.trigger(item);

    // Wait until rst_n (a 4-state value) is equal to ~cur_val, ignoring any transitions to x or z.
    wait(m_vif.rst_n == ~cur_val);
  end
endtask
