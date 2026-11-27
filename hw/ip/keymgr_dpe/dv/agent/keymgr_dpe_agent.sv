// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This agent is active in block-level simulation to drive the input side of the keymgr_dpe. For
// top-level simulation, it is passive and only monitors the interface.
class keymgr_dpe_agent extends dv_base_agent #(.CFG_T      (keymgr_dpe_agent_cfg),
                                               .DRIVER_T   (keymgr_dpe_driver),
                                               .SEQUENCER_T(keymgr_dpe_sequencer),
                                               .MONITOR_T  (keymgr_dpe_monitor));
  `uvm_component_utils(keymgr_dpe_agent)

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass

function keymgr_dpe_agent::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void keymgr_dpe_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // The environment is responsible for setting the vif for this agent. If it hasn't done so, try
  // the config DB for the agent's scope, and fail if the vif isn't there.
  if (cfg.m_vif == null &&
      !uvm_config_db#(virtual keymgr_dpe_if)::get(this, "", "vif", cfg.m_vif))
    `uvm_fatal(get_full_name(), "Failed to get vif from uvm_config_db")

  // If the agent is active, the interface's is_active bit must also be set. Otherwise the
  // interface releases its wires ('z) and the values driven on the *_internal signals never reach
  // the DUT.
  if (cfg.is_active && !cfg.m_vif.is_active)
    `uvm_error(get_full_name(), "Agent is active but the interface's is_active bit is false.")

  // Set the sequencer handle later used by keymgr_dpe_base_vseq.
  if (cfg.is_active) cfg.set_sequencer(sequencer);
endfunction
