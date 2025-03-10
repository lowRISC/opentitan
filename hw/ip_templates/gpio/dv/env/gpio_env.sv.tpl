// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_env extends cip_base_env #(
  .CFG_T              (${module_instance_name}_env_cfg),
  .COV_T              (${module_instance_name}_env_cov),
  .VIRTUAL_SEQUENCER_T(${module_instance_name}_virtual_sequencer),
  .SCOREBOARD_T       (${module_instance_name}_scoreboard)
  );
  `uvm_component_utils(${module_instance_name}_env)

  ${module_instance_name}_strap_agent   strap_agent;
  straps_vif         m_straps_vif;
  virtual clk_rst_if m_clk_rst_vif;
  ${module_instance_name}_vif           m_${module_instance_name}_vif;

  function new (string name, uvm_component parent = null);
    super.new (name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create and configure the ${module_instance_name}_strap_agent
    strap_agent = ${module_instance_name}_strap_agent::type_id::create("strap_agent", this);

    if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", m_straps_vif)) begin
      `uvm_fatal("${module_instance_name}_strap_driver", "Could not get m_straps_vif from uvm_config_db ")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_rst_vif", m_clk_rst_vif)) begin
      `uvm_fatal("${module_instance_name}_strap_driver", "Could not get m_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(${module_instance_name}_vif)::get(this, "", "${module_instance_name}_vif", m_${module_instance_name}_vif)) begin
      `uvm_fatal("${module_instance_name}_strap_driver", "Could not get m_${module_instance_name}_vif from uvm_config_db")
    end
    // Set these interfaces instances to the environment configuration object.
    cfg.${module_instance_name}_vif        = m_${module_instance_name}_vif;
    cfg.straps_vif_inst = m_straps_vif;
    cfg.clk_rst_vif     = m_clk_rst_vif;

  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect the strap monitor to the ${module_instance_name} scoreboard
    strap_agent.strap_monitor.mon_ap.connect(scoreboard.sb_exp);
    // Register a strap agent sub-sequencer into the virtual sequencer.
    // to be able to access it through the main sequence test.
    virtual_sequencer.register_sequencer("strap_sequencer", strap_agent.strap_sqr);
  endfunction
endclass