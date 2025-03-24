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

  gpio_strap_agent   m_strap_agent;
  straps_vif         m_straps_vif;
  virtual clk_rst_if m_clk_rst_vif;
  gpio_vif           m_gpio_vif;

  function new (string name, uvm_component parent = null);
    super.new (name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create and configure the gpio_strap_agent
    m_strap_agent = gpio_strap_agent::type_id::create("m_strap_agent", this);

    if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", m_straps_vif)) begin
      `uvm_fatal("gpio_strap_driver", "Could not get m_straps_vif from uvm_config_db ")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_rst_vif", m_clk_rst_vif)) begin
      `uvm_fatal("gpio_strap_driver", "Could not get m_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", m_gpio_vif)) begin
      `uvm_fatal("gpio_strap_driver", "Could not get m_gpio_vif from uvm_config_db")
    end
    // Set these interfaces instances to the environment configuration object.
    cfg.gpio_vif        = m_gpio_vif;
    cfg.straps_vif_inst = m_straps_vif;
    cfg.clk_rst_vif     = m_clk_rst_vif;
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect the strap monitor to the scoreboard
    m_strap_agent.strap_monitor.mon_ap.connect(scoreboard.analysis_port);
    // Register a strap agent sub-sequencer into the virtual sequencer
    // to be able to access it through the main sequence test.
    virtual_sequencer.register_sequencer("strap_sequencer", m_strap_agent.strap_sqr);
  endfunction
endclass
