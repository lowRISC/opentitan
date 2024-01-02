// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_env extends cip_base_env #(
  .CFG_T              (dma_env_cfg),
  .COV_T              (dma_env_cov),
  .VIRTUAL_SEQUENCER_T(dma_virtual_sequencer),
  .SCOREBOARD_T       (dma_scoreboard)
);
  `uvm_component_utils(dma_env)

  `uvm_component_new

  // TL Agents
  tl_agent tl_agent_dma_host;
  tl_agent tl_agent_dma_ctn;
  tl_agent tl_agent_dma_sys;

  // PHASE - BUILD
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    // Set the synchronise_ports flag on each of the TL agent configs
    // This makes sure that the order of tl_seq_item sent from monitor
    // is always A channel item first and then D channel item
    cfg.tl_agent_dma_host_cfg.synchronise_ports = 1'b1;
    cfg.tl_agent_dma_ctn_cfg.synchronise_ports = 1'b1;
    cfg.tl_agent_dma_sys_cfg.synchronise_ports  = 1'b1;

    // The SoC System bus does not have a TL-style 'ready' signal on the address channel.
    cfg.tl_agent_dma_sys_cfg.a_ready_delay_min = 0;
    cfg.tl_agent_dma_sys_cfg.a_ready_delay_max = 0;

    // Get dma interface
    if (!uvm_config_db#(dma_vif)::get(this, "", "dma_vif", cfg.dma_vif)) begin
      `uvm_fatal(`gfn, "failed to get dma_vif from uvm_config_db")
    end
    // Get SoC System bus <-> TL-UL adapter interface
    if (!uvm_config_db#(dma_sys_tl_vif)::get(this, "", "dma_sys_tl_vif", cfg.dma_sys_tl_vif)) begin
      `uvm_fatal(`gfn, "failed to get dma_sys_tl_vif from uvm_config_db")
    end

    // Host agent
    tl_agent_dma_host = tl_agent::type_id::create("tl_agent_dma_host", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "tl_agent_dma_host", "cfg", cfg.tl_agent_dma_host_cfg);
    // CTN agent
    tl_agent_dma_ctn = tl_agent::type_id::create("tl_agent_dma_ctn", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "tl_agent_dma_ctn", "cfg", cfg.tl_agent_dma_ctn_cfg);
    // SYS agent
    tl_agent_dma_sys = tl_agent::type_id::create("tl_agent_dma_sys", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "tl_agent_dma_sys", "cfg", cfg.tl_agent_dma_sys_cfg);

  endfunction: build_phase

  // PHASE - CONNECT
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // Update virtual sequencer handles
    virtual_sequencer.tl_sequencer_dma_host_h = tl_agent_dma_host.sequencer;
    virtual_sequencer.tl_sequencer_dma_ctn_h = tl_agent_dma_ctn.sequencer;
    virtual_sequencer.tl_sequencer_dma_sys_h  = tl_agent_dma_sys.sequencer;
    // Connect host tl_monitor ports to scoreboard analysis_fifo
    tl_agent_dma_host.monitor.a_chan_port.connect(
        scoreboard.tl_a_chan_fifos[cfg.dma_a_fifo["host"]].analysis_export);
    tl_agent_dma_host.monitor.d_chan_port.connect(
        scoreboard.tl_d_chan_fifos[cfg.dma_d_fifo["host"]].analysis_export);
    tl_agent_dma_host.monitor.channel_dir_port.connect(
        scoreboard.tl_dir_fifos[cfg.dma_dir_fifo["host"]].analysis_export);
    // Connect ctn tl_monitor ports to scoreboard analysis_fifo
    tl_agent_dma_ctn.monitor.a_chan_port.connect(
        scoreboard.tl_a_chan_fifos[cfg.dma_a_fifo["ctn"]].analysis_export);
    tl_agent_dma_ctn.monitor.d_chan_port.connect(
        scoreboard.tl_d_chan_fifos[cfg.dma_d_fifo["ctn"]].analysis_export);
    tl_agent_dma_ctn.monitor.channel_dir_port.connect(
        scoreboard.tl_dir_fifos[cfg.dma_dir_fifo["ctn"]].analysis_export);
    // Connect sys tl_monitor ports to scoreboard analysis_fifo
    tl_agent_dma_sys.monitor.a_chan_port.connect(
        scoreboard.tl_a_chan_fifos[cfg.dma_a_fifo["sys"]].analysis_export);
    tl_agent_dma_sys.monitor.d_chan_port.connect(
        scoreboard.tl_d_chan_fifos[cfg.dma_d_fifo["sys"]].analysis_export);
    tl_agent_dma_sys.monitor.channel_dir_port.connect(
        scoreboard.tl_dir_fifos[cfg.dma_dir_fifo["sys"]].analysis_export);
  endfunction: connect_phase

  // Display sequencer fifo connections for debug
  function void display_sequencer_connections();
    virtual_sequencer.tl_sequencer_dma_host_h.a_chan_req_fifo.analysis_export.debug_provided_to();
    virtual_sequencer.tl_sequencer_dma_ctn_h.a_chan_req_fifo.analysis_export.debug_provided_to();
    virtual_sequencer.tl_sequencer_dma_sys_h.a_chan_req_fifo.analysis_export.debug_provided_to();
  endfunction

  // Display TL agent port connections for debug
  function void display_agent_connections();
    // DEBUG Host agent
    `uvm_info(`gfn, "[CONNECTION] Host agent driver debug - FANOUT", UVM_HIGH)
    tl_agent_dma_host.driver.seq_item_port.debug_connected_to();
    `uvm_info(`gfn, "[CONNECTION] Host agent sequencer debug - FANIN", UVM_HIGH)
    tl_agent_dma_host.sequencer.seq_item_export.debug_provided_to();
    `uvm_info(`gfn, "[CONNECTION] Host agent monitor debug - FANOUT", UVM_HIGH)
    tl_agent_dma_host.monitor.a_chan_port.debug_connected_to();
    `uvm_info(`gfn, "[CONNECTION] CTN agent driver debug - FANOUT", UVM_HIGH)
    tl_agent_dma_ctn.driver.seq_item_port.debug_connected_to();
    `uvm_info(`gfn, "[CONNECTION] CTN agent sequencer debug - FANIN", UVM_HIGH)
    tl_agent_dma_ctn.sequencer.seq_item_export.debug_provided_to();
    `uvm_info(`gfn, "[CONNECTION] CTN agent monitor debug - FANOUT", UVM_HIGH)
    tl_agent_dma_ctn.monitor.a_chan_port.debug_connected_to();
    `uvm_info(`gfn, "[CONNECTION] SYS agent driver debug - FANOUT", UVM_HIGH)
    tl_agent_dma_sys.driver.seq_item_port.debug_connected_to();
    `uvm_info(`gfn, "[CONNECTION] SYS agent sequencer debug - FANIN", UVM_HIGH)
    tl_agent_dma_sys.sequencer.seq_item_export.debug_provided_to();
    `uvm_info(`gfn, "[CONNECTION] SYS agent monitor debug - FANOUT", UVM_HIGH)
    tl_agent_dma_sys.monitor.a_chan_port.debug_connected_to();
  endfunction

  // Display scoreboard analysis fifo connections for debug
  function void display_scoreboard_connections(string intf_name);
    `uvm_info(`gfn, $sformatf("[CONNECTION] SCB DEBUG %s agent - FANIN", intf_name), UVM_HIGH)
    scoreboard.tl_a_chan_fifos[cfg.dma_a_fifo[intf_name]].analysis_export.debug_provided_to();
    scoreboard.tl_d_chan_fifos[cfg.dma_d_fifo[intf_name]].analysis_export.debug_provided_to();
    scoreboard.tl_dir_fifos[cfg.dma_dir_fifo[intf_name]].analysis_export.debug_provided_to();
  endfunction

  //  Display port connections in DV environment
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    if (uvm_report_enabled(UVM_HIGH)) begin
      foreach (cfg.dma_a_fifo[key]) begin
        display_scoreboard_connections(key);
      end
      display_agent_connections();
      display_sequencer_connections();
    end
  endfunction: start_of_simulation_phase
endclass
