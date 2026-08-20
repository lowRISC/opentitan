// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A general agent that represents an escalation interface.

class esc_agent extends dv_reactive_agent #(
    .CFG_T           (esc_agent_cfg),
    .DRIVER_T        (dv_base_driver #(esc_seq_item, esc_agent_cfg)),
    .HOST_DRIVER_T   (esc_sender_driver),
    .DEVICE_DRIVER_T (esc_receiver_driver),
    .SEQUENCER_T     (esc_sequencer),
    .MONITOR_T       (esc_monitor),
    .COV_T           (esc_agent_cov)
  );

  `uvm_component_utils(esc_agent)

  // An output port that reports escalation items that have been seen.
  uvm_analysis_port #(esc_seq_item) m_esc_port;

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);

endclass : esc_agent

function esc_agent::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void esc_agent::build_phase(uvm_phase phase);
  esc_agent_cfg cfg;
  if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
    `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
  end

  super.build_phase(phase);

  m_esc_port = new("m_esc_port", this);

  if (!uvm_config_db#(virtual esc_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(`gfn, "failed to get esc_if handle from uvm_config_db")
  end

  // get esc_en signal for esc_monitor
  if (cfg.is_active && cfg.if_mode == Device) begin
    if (!uvm_config_db#(virtual esc_probe_if)::get(this, "", "probe_vif", cfg.probe_vif)) begin
        `uvm_fatal(`gfn, "failed to get probe_vif handle from uvm_config_db")
    end
  end

  // Set variables that configure the escalation interface
  cfg.vif.is_async  = cfg.is_async;
  cfg.vif.is_active = cfg.is_active;
  cfg.vif.if_mode   = cfg.if_mode;
endfunction : build_phase
