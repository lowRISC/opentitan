// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// ibex processor core environment class
// ---------------------------------------------
class core_ibex_env extends uvm_env;

  tl_agent           data_if_device_agent;
  tl_agent           instr_if_device_agent;
  core_ibex_vseqr    vseqr;
  core_ibex_env_cfg  cfg;

  `uvm_component_utils(core_ibex_env)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(core_ibex_env_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal("NO_CFG", {"cfg must be set for:", get_full_name(), ".cfg"});
    end
    uvm_config_db#(tl_agent_cfg)::set(this, "*data_if_device_agent*", "cfg",
                                      cfg.data_if_agent_cfg);
    uvm_config_db#(tl_agent_cfg)::set(this, "*instr_if_device_agent*", "cfg",
                                      cfg.instr_if_agent_cfg);
    data_if_device_agent = tl_agent::type_id::create("data_if_device_agent", this);
    instr_if_device_agent = tl_agent::type_id::create("instr_if_device_agent", this);
    // Create virtual sequencer
    vseqr = core_ibex_vseqr::type_id::create("vseqr", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    vseqr.data_if_seqr = data_if_device_agent.seqr;
    vseqr.instr_if_seqr = instr_if_device_agent.seqr;
  endfunction : connect_phase

endclass
