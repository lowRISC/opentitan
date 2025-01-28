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
  gpio_base_sequencer v_sequencer;
  straps_vif straps_vif_inst;
  gpio_vif _vif;
  
  
  function new (string name, uvm_component parent = null);
    super.new (name, parent);
  endfunction

  // TODO: The virtual interfaces instances should be inside the cfg class??
  function void build_phase(uvm_phase phase);

    v_sequencer = gpio_base_sequencer #(gpio_seq_item, 
                                        gpio_strap_agent_cfg, 
                                        gpio_seq_item)::type_id::create("v_sequencer", this);
                                        
    super.virtual_sequencer = v_sequencer;

    // Set the gpio_strap_agent_cfg in database
    uvm_config_db#(gpio_base_sequencer)::set(this, "*", "v_sequencer", v_sequencer);
    
    `uvm_info(get_full_name(), "Create and configure the gpio_strap_agent_cfg", UVM_HIGH)

    // Create and configure the gpio_strap_agent_cfg
    agent_cfg = gpio_strap_agent_cfg::type_id::create("agent_cfg");
    
    // Set the gpio_strap_agent_cfg in database
    uvm_config_db#(gpio_strap_agent_cfg)::set(this, "*", "cfg", agent_cfg);
    
    strap_agent = gpio_strap_agent::type_id::create("strap_agent", this);

    // Get the gpio_vif from the uvm_config_db
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", _vif)) begin
      `uvm_fatal(get_full_name(), "failed to get gpio_vif from uvm_config_db")
    end

    // get dv_base_env_cfg object from uvm_config_db
    if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
    end

    cfg.gpio_vif = _vif;

    super.build_phase(phase);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    strap_agent.strap_monitor.mon_ap.connect(scoreboard.sb_exp);
    v_sequencer.strap_sqr_h = strap_agent.strap_sqr;
  endfunction

endclass
