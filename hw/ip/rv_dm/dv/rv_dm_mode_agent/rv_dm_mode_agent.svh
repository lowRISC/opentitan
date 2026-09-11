// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_mode_agent extends dv_base_agent #(.CFG_T      (rv_dm_mode_agent_cfg),
                                               .DRIVER_T   (rv_dm_mode_driver),
                                               .SEQUENCER_T(rv_dm_mode_sequencer),
                                               .MONITOR_T  (rv_dm_mode_monitor));
  `uvm_component_utils(rv_dm_mode_agent)

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass

function rv_dm_mode_agent::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void rv_dm_mode_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // If cfg.vif isn't already supplied, look up a vif interface handle in the config db.
  if (cfg.vif == null &&
      !uvm_config_db#(virtual rv_dm_mode_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(get_full_name(), "Failed to get vif from from uvm_config_db")
  end

  // If the agent is configured to be active, make sure that the is_active flag in the interface is
  // also set: if it isn't our updates to the *_internal signals will have no effect.
  if (cfg.is_active && !cfg.vif.is_active) begin
    `uvm_error(get_full_name(), "Agent is active but the interface's is_active signal is false.")
  end
endfunction
