// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_env extends dv_base_env #(
    .CFG_T              (ibex_icache_env_cfg),
    .COV_T              (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T(ibex_icache_virtual_sequencer),
    .SCOREBOARD_T       (ibex_icache_scoreboard)
  );
  `uvm_component_utils(ibex_icache_env)

  ibex_icache_core_agent core_agent;
  ibex_icache_mem_agent  mem_agent;
  scrambling_key_agent   scrambling_key_agent_h;

  // Heartbeat tracking
  uvm_callbacks_objection           hb_objection;
  uvm_heartbeat                     heartbeat;
  uvm_event                         hb_event;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    core_agent = ibex_icache_core_agent::type_id::create("core_agent", this);
    uvm_config_db#(ibex_icache_core_agent_cfg)::set(this, "core_agent*", "cfg", cfg.core_agent_cfg);

    mem_agent = ibex_icache_mem_agent::type_id::create("mem_agent", this);
    uvm_config_db#(ibex_icache_mem_agent_cfg)::set(this, "mem_agent*", "cfg", cfg.mem_agent_cfg);
    scrambling_key_agent_h = scrambling_key_agent::type_id::create("scrambling_key_agent_h", this);
    uvm_config_db#(scrambling_key_agent_cfg)::set(this, "scrambling_key_agent_h", "cfg",
                                                  cfg.scrambling_key_cfg);
    cfg.scrambling_key_cfg.agent_type = push_pull_agent_pkg::PullAgent;
    cfg.scrambling_key_cfg.if_mode = dv_utils_pkg::Device;

    hb_objection = new("hb_objection");
    heartbeat    = new("heartbeat", this, hb_objection);
    hb_event     = new("hb_event");

    cfg.clk_rst_vif.set_sole_clock();
    if (!uvm_config_db#(ibex_icache_ram_vif)::get(this, "", "vif", cfg.ram_if)) begin
      `uvm_fatal(`gfn, "failed to get ibex_icache_ram_vif handle from uvm_config_db")
    end

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      core_agent.monitor.analysis_port.connect(scoreboard.core_fifo.analysis_export);
      mem_agent.monitor.analysis_port.connect(scoreboard.mem_fifo.analysis_export);
      core_agent.driver.analysis_port.connect(scoreboard.seed_fifo.analysis_export);
    end

    // If we are active, wire up each active agent to a sequencer in the virtual sequencer.
    if (cfg.is_active) begin
      if (cfg.mem_agent_cfg.is_active && cfg.core_agent_cfg.is_active) begin
        core_agent.driver.analysis_port.connect(mem_agent.sequencer.seed_fifo.analysis_export);
      end

      if (cfg.core_agent_cfg.is_active) begin
        virtual_sequencer.core_sequencer_h = core_agent.sequencer;
      end
      if (cfg.mem_agent_cfg.is_active) begin
        virtual_sequencer.mem_sequencer_h = mem_agent.sequencer;
      end

    end

    // Register the heartbeat objection with both sequencers (so they know how to reset it)
    core_agent.sequencer.register_hb(hb_objection);
    mem_agent.sequencer.register_hb(hb_objection);

    // Add each sequencer to the heartbeat object. This means that the heartbeat object expects one
    // or more of them to set the objection each time around.
    void'(heartbeat.set_mode(UVM_ANY_ACTIVE));
    heartbeat.add(core_agent.sequencer);
    heartbeat.add(mem_agent.sequencer);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    // Start the heartbeat monitor. This will check (and then clear) objections each time hb_event
    // is triggered.
    heartbeat.start(hb_event);
    forever begin
      // Every 2000 clocks, check the heartbeat monitor (not stopping early on reset)
      cfg.core_agent_cfg.vif.wait_clks(2000, 1'b0);
      hb_event.trigger();
    end
  endtask

endclass
