// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_env extends cip_base_env #(
    .CFG_T              (rom_ctrl_env_cfg),
    .COV_T              (rom_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(rom_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (rom_ctrl_scoreboard)
  );
  `uvm_component_utils(rom_ctrl_env)

  `uvm_component_new

  // KMAC interface agent
  kmac_app_device_agent m_kmac_agent;

  // A passive reset_agent that can be used to watch whether rom_ctrl is in reset. Get this with
  // get_reset_agent().
  local reset_agent m_reset_agent;

  // A sequencer and driver for forcing the count in the FSM's u_counter. Both are created in
  // build_phase, but only if cfg.get_skip_middle() is true.
  local rom_ctrl_addr_force_sequencer_t m_addr_force_sequencer;
  local rom_ctrl_addr_force_driver      m_addr_force_driver;

  // A sequencer and driver for forcing the digest that comes back from kmac. Both are created in
  // build_phase.
  local rom_ctrl_kmac_rsp_force_sequencer_t m_kmac_rsp_force_sequencer;
  local rom_ctrl_kmac_rsp_force_driver      m_kmac_rsp_force_driver;

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);

  // Get the reset_agent
  extern function reset_agent get_reset_agent();

  // Get the m_addr_force_sequencer handle.
  //
  // This will fail if m_addr_force_sequencer is null (because cfg.get_skip_middle is false)
  extern function rom_ctrl_addr_force_sequencer_t get_addr_force_sequencer();

  // Get the m_kmac_rsp_force_sequencer handle.
  //
  // This will fail if m_kmac_rsp_force_sequencer is null (because cfg.get_force_expected_kmac_rsp
  // returned false)
  extern function rom_ctrl_kmac_rsp_force_sequencer_t get_kmac_rsp_force_sequencer();
endclass

function void rom_ctrl_env::build_phase(uvm_phase phase);
  virtual rom_ctrl_if vif;
  bit integrity_check_disabled;

  // Get the main bound-in rom_ctrl interface, writing it to a local variable for now (because cfg
  // is only created by dv_base_env::build_phase).
  if (!uvm_config_db#(rom_ctrl_vif)::get(this, "", "rom_ctrl_vif", vif))
    `uvm_fatal("config_db", "Failed to get rom_ctrl_vif from uvm_config_db")

  // When the dv_base_env::build_phase runs, it will try to look up clock/reset interfaces for the
  // two RAL names. Pass them explicitly through uvm_config_db (we can't do this through cfg because
  // it hasn't yet been created).
  uvm_config_db#(virtual clk_rst_if)::set(this, "", "clk_rst_vif", vif.u_clk_rst_if);
  uvm_config_db#(virtual clk_rst_if)::set(this, "", "clk_rst_vif_rom_ctrl_prim_reg_block",
                                          vif.u_rom_clk_rst_if);

  super.build_phase(phase);

  // Now we actually have a cfg object, set its rom_ctrl_vif. Also, tell that interface whether the
  // environment is active.
  cfg.rom_ctrl_vif = vif;
  cfg.rom_ctrl_vif.set_active(cfg.is_active);

  // Get the rom_bkdr interface.
  if (!uvm_config_db#(rom_ctrl_bkdr_util)::get(this, "", "rom_ctrl_bkdr_util",
                                               cfg.rom_ctrl_bkdr_util_h))
    `uvm_fatal("config_db", "Failed to get rom_ctrl_bkdr_util from uvm_config_db")

  // Check whether the integrity check has been disabled (because DISABLE_ROM_INTEGRITY_CHECK was
  // defined).
  if (!uvm_config_db#(bit)::get(this, "",
                                "integrity_check_disabled", integrity_check_disabled)) begin
    `uvm_fatal("config_db", "Failed to get integrity_check_disabled flag from uvm_config_db.")
  end

  // If the integrity check has not been disabled, get the bound-in FSM interface. If it *is*
  // disabled, this will be visible through cfg by fsm_vif being null.
  if (!integrity_check_disabled) begin
    if (!uvm_config_db#(virtual rom_ctrl_fsm_if)::get(this, "",
                                                      "rom_ctrl_fsm_vif", cfg.fsm_vif)) begin
      `uvm_fatal("config_db", "Failed to get rom_ctrl_fsm_vif from uvm_config_db.")
    end
  end

  // If the environment is active, get hold of an interface that is bound into the compare module
  // (because sequences will want to use it to inject faults).
  if (cfg.is_active) begin
    if (!uvm_config_db#(virtual rom_ctrl_compare_if)::get(this, "", "rom_ctrl_compare_vif",
                                                          cfg.compare_vif))
      `uvm_fatal("config_db",
                 "Active environment could not get rom_ctrl_compare_vif from uvm_config_db")
  end

  // Provide interfaces for the TileLink agents
  uvm_config_db#(virtual tl_if)::set(this, "m_tl_agent_rom_ctrl_prim_reg_block", "vif",
                                     cfg.rom_ctrl_vif.u_tl_rom_if);
  uvm_config_db#(virtual tl_if)::set(this, "m_tl_agent_rom_ctrl_regs_reg_block", "vif",
                                     cfg.rom_ctrl_vif.u_tl_regs_if);

  // Provide an interface for the alert agent
  uvm_config_db#(virtual alert_if)::set(this, "m_alert_agent_fatal", "vif",
                                        cfg.rom_ctrl_vif.u_alert_if);

  // Build the KMAC agent
  m_kmac_agent = kmac_app_device_agent::type_id::create("m_kmac_agent", this);
  cfg.m_kmac_agent_cfg.vif = cfg.rom_ctrl_vif.u_kmac_app_if;
  uvm_config_db#(kmac_app_agent_cfg)::set(this, "m_kmac_agent", "cfg", cfg.m_kmac_agent_cfg);

  // Build the reset agent to track the current reset state
  m_reset_agent = reset_agent::type_id::create("m_reset_agent", this);
  uvm_config_db#(virtual clk_rst_if)::set(this, "m_reset_agent", "vif", cfg.clk_rst_vif);

  // Create a sequencer and driver for forcing the counter in the rom_ctrl FSM, but only if
  // cfg.get_skip_middle() is true (and fsm_vif is non-null, meaning that rom_ctrl is actually doing
  // any integrity checking).
  //
  // Note that this does *not* depend on cfg.is_active: this "backdoor trickery" works by accessing
  // internals of rom_ctrl and doesn't interact with outside stimulus. As such, it makes perfect
  // sense to use when the environment is bound into a higher level testbench.
  if (cfg.get_skip_middle() && cfg.fsm_vif != null) begin
    m_addr_force_sequencer = (rom_ctrl_addr_force_sequencer_t::type_id::
                              create("m_addr_force_sequencer", this));

    m_addr_force_driver = rom_ctrl_addr_force_driver::type_id::create("m_addr_force_driver", this);
  end

  // Create a sequencer and driver for overriding responses from kmac, but only if
  // cfg.get_force_expected_kmac_rsp() is true.
  //
  // As with m_addr_force_sequencer, this only runs if fsm_vif is non-null (meaning that rom_ctrl is
  // actually sending anything to kmac).
  //
  // Also as with m_addr_force_sequencer, this does *not* depend on cfg.is_active: it is similarly
  // relevant when bound into a higher level testbench.
  if (cfg.get_force_expected_kmac_rsp() && cfg.fsm_vif != null) begin
    m_kmac_rsp_force_sequencer = (rom_ctrl_kmac_rsp_force_sequencer_t::type_id::
                                  create("m_kmac_rsp_force_sequencer", this));
    m_kmac_rsp_force_driver =
      rom_ctrl_kmac_rsp_force_driver::type_id::create("m_kmac_rsp_force_driver", this);
  end

  cfg.scoreboard = scoreboard;

endfunction

function void rom_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  m_kmac_agent.monitor.m_req_packet_analysis_port.connect(scoreboard.m_kmac_req_imp);
  m_kmac_agent.monitor.analysis_port.connect(scoreboard.m_kmac_txn_imp);

  if (cfg.is_active) begin
    virtual_sequencer.kmac_sequencer_h = m_kmac_agent.sequencer;
  end

  // If there is an address forcing driver (because cfg.get_skip_middle() was true and the existence
  // of fsm_vif means that there is integrity checking), connect the address forcing driver whether
  // or not the environment is active: we want to be able to use it to convince rom_ctrl by the back
  // door to jump over the middle of ROM.
  if (m_addr_force_driver != null) begin
    m_addr_force_driver.set_vif(cfg.fsm_vif);
    m_addr_force_driver.seq_item_port.connect(m_addr_force_sequencer.seq_item_export);
  end

  // If there is a KMAC response forcing driver (because cfg.get_force_expected_kmac_rsp() was
  // true), connect the kmac response forcing driver whether or not the environment is active. As
  // with m_addr_force_driver, we want to be able to use it to convince rom_ctrl by the back door to
  // override digests coming back from kmac.
  if (m_kmac_rsp_force_driver != null) begin
    m_kmac_rsp_force_driver.set_vif(cfg.fsm_vif);
    m_kmac_rsp_force_driver.seq_item_port.connect(m_kmac_rsp_force_sequencer.seq_item_export);
  end
endfunction

function reset_agent rom_ctrl_env::get_reset_agent();
  return m_reset_agent;
endfunction

function rom_ctrl_addr_force_sequencer_t rom_ctrl_env::get_addr_force_sequencer();
  if (m_addr_force_sequencer == null) begin
    `uvm_fatal("no_addr_force_sequencer", "No sequencer to return: was cfg.get_skip_middle false?")
  end
  return m_addr_force_sequencer;
endfunction

function rom_ctrl_kmac_rsp_force_sequencer_t rom_ctrl_env::get_kmac_rsp_force_sequencer();
  if (m_kmac_rsp_force_sequencer == null) begin
    `uvm_fatal("no_kmac_rsp_force_sequencer",
               "No sequencer to return: was cfg.get_force_expected_kmac_rsp false?")
  end
  return m_kmac_rsp_force_sequencer;
endfunction
