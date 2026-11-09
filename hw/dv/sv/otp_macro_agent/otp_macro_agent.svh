// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An agent for the OTP macro interface (otp_macro_if).
//
// When active, it acts as otp_ctrl: sequences such as otp_macro_cmd_seq pick commands (Init,
// Read, Write, ReadRaw, WriteRaw and Zeroize) and otp_macro_driver sends them to the block that
// stores the OTP contents. When passive, it only watches the interface. Either way, each completed
// transaction is written to analysis_port.

class otp_macro_agent extends dv_base_agent #(.CFG_T       (otp_macro_agent_cfg),
                                              .DRIVER_T    (otp_macro_driver),
                                              .SEQUENCER_T (otp_macro_sequencer),
                                              .MONITOR_T   (otp_macro_monitor));
  `uvm_component_utils(otp_macro_agent)

  // Completed transactions, from the monitor
  uvm_analysis_port #(otp_macro_rsp_seq_item) analysis_port;

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass

function otp_macro_agent::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void otp_macro_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  analysis_port = new("analysis_port", this);

  // If cfg.m_vif isn't already supplied, look up a vif interface handle in the config db.
  if (cfg.m_vif == null &&
      !uvm_config_db#(virtual otp_macro_if)::get(this, "", "vif", cfg.m_vif)) begin
    `uvm_fatal("no_vif", "Failed to get vif from uvm_config_db")
  end

  // This agent can send requests (Host) or watch the interface (Monitor), but cannot respond to
  // requests.
  if (cfg.if_mode == dv_utils_pkg::Device) begin
    `uvm_fatal("unsupported_mode", "This agent cannot respond to OTP macro requests.")
  end
  if (cfg.is_active && cfg.if_mode != dv_utils_pkg::Host) begin
    `uvm_fatal("unsupported_mode", "An active agent must have if_mode = Host.")
  end

  // The interface only drives the request when the agent is active.
  cfg.m_vif.if_mode = cfg.is_active ? dv_utils_pkg::Host : dv_utils_pkg::Monitor;
endfunction

function void otp_macro_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  monitor.analysis_port.connect(analysis_port);
endfunction
