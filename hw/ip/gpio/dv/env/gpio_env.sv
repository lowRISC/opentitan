// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_env extends cip_base_env #(
  .CFG_T              (gpio_env_cfg),
  .COV_T              (gpio_env_cov),
  .VIRTUAL_SEQUENCER_T(gpio_virtual_sequencer),
  .SCOREBOARD_T       (gpio_scoreboard)
);
  `uvm_component_utils(gpio_env)

  gpio_strap_agent strap_agent;
  gpio_strap_agent_cfg agent_cfg;
  
  
  function new (string name, uvm_component parent = null);
    super.new (name, parent);
  endfunction

  // TODO: The virtual interfaces instances should be inside the cfg class??
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    `uvm_info(get_full_name(), "Create and configure the gpio_strap_agent_cfg", UVM_HIGH)

    // Create and configure the gpio_strap_agent_cfg
    agent_cfg = gpio_strap_agent_cfg::type_id::create("agent_cfg");
    
    // Set the gpio_strap_agent_cfg in database
    uvm_config_db#(gpio_strap_agent_cfg)::set(this, "*", "cfg", agent_cfg);
    
    `uvm_info(get_full_name(), "Agent cfg setted in the uvm_config_db", UVM_HIGH)

    strap_agent = gpio_strap_agent::type_id::create("strap_agent", this);

    `uvm_info(get_full_name(), "Agent created", UVM_HIGH)
    
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", cfg.gpio_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get gpio_vif from uvm_config_db")
    end
    if (!uvm_config_db#(straps_vif)::get(this, "", "straps_vif", cfg.straps_vif_inst)) begin
      `uvm_fatal(get_full_name(), "Virtual interface straps_vif_inst is not set")
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    strap_agent.strap_monitor.mon_ap.connect(scoreboard.sb_exp);
  endfunction

endclass
