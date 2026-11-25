// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_macro_agent extends dv_base_agent #(.CFG_T      (rram_macro_agent_cfg),
                                               .MONITOR_T  (rram_macro_monitor));
  `uvm_component_utils(rram_macro_agent)

  // An analysis port that reports transactions that have been seen
  uvm_analysis_port #(rram_macro_rsp_seq_item) m_analysis_port;

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass

function rram_macro_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void rram_macro_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // If cfg.m_vif isn't already supplied, look up a vif interface handle in the config db.
  if (cfg.m_vif == null &&
      !uvm_config_db#(virtual rram_macro_if)::get(this, "", "vif", cfg.m_vif)) begin
    `uvm_fatal("no_vif", "Failed to get vif from uvm_config_db")
  end

  m_analysis_port = new("m_analysis_port", this);

  // This agent only supports Monitor mode (passive)
  if (cfg.if_mode != dv_utils_pkg::Monitor) begin
    `uvm_fatal("unsupported_mode", "This agent only supports Monitor mode.")
  end
endfunction

function void rram_macro_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  monitor.analysis_port.connect(m_analysis_port);
endfunction
