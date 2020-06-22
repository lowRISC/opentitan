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

  ibex_icache_ecc_agent  ecc_tag_agents[];
  ibex_icache_ecc_agent  ecc_data_agents[];

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

    // If ECC is enabled, create ECC agents for the RAMs. We have already created config objects for
    // them (the test called create_ecc_agent_cfgs in its build_phase method), so we just have to
    // make an agent for each config. In practice, there will be the same number of tag and data
    // agents, but this code doesn't really care.
    ecc_tag_agents  = new[cfg.ecc_tag_agent_cfgs.size()];
    for (int unsigned i = 0; i < cfg.ecc_tag_agent_cfgs.size(); i++) begin
      string tname = $sformatf("ecc_tag_agents[%0d]", i);
      ecc_tag_agents[i] = ibex_icache_ecc_agent::type_id::create(tname, this);
      uvm_config_db#(ibex_icache_ecc_agent_cfg)::set(this, {tname, "*"}, "cfg", cfg.ecc_tag_agent_cfgs[i]);
    end
    ecc_data_agents  = new[cfg.ecc_data_agent_cfgs.size()];
    for (int unsigned i = 0; i < cfg.ecc_data_agent_cfgs.size(); i++) begin
      string dname = $sformatf("ecc_data_agents[%0d]", i);
      ecc_data_agents[i] = ibex_icache_ecc_agent::type_id::create(dname, this);
      uvm_config_db#(ibex_icache_ecc_agent_cfg)::set(this, {dname, "*"}, "cfg", cfg.ecc_data_agent_cfgs[i]);
    end

    hb_objection = new("hb_objection");
    heartbeat    = new("heartbeat", this, hb_objection);
    hb_event     = new("hb_event");

    cfg.clk_rst_vif.set_sole_clock();
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

      // We assume that either all ECC tag/data agents are active or none of them are.
      `DV_CHECK_EQ_FATAL(cfg.ecc_tag_agent_cfgs.size(), ecc_tag_agents.size())
      if ((cfg.ecc_tag_agent_cfgs.size() > 0) && (cfg.ecc_tag_agent_cfgs[0].is_active)) begin
        virtual_sequencer.ecc_tag_sequencers = new[cfg.ecc_tag_agent_cfgs.size()];
        foreach (ecc_tag_agents[i]) begin
          `DV_CHECK_FATAL(cfg.ecc_tag_agent_cfgs[i].is_active);
          virtual_sequencer.ecc_tag_sequencers[i] = ecc_tag_agents[i].sequencer;
        end
      end
      `DV_CHECK_EQ_FATAL(cfg.ecc_data_agent_cfgs.size(), ecc_data_agents.size())
      if ((cfg.ecc_data_agent_cfgs.size() > 0) && (cfg.ecc_data_agent_cfgs[0].is_active)) begin
        virtual_sequencer.ecc_data_sequencers = new[cfg.ecc_data_agent_cfgs.size()];
        foreach (ecc_data_agents[i]) begin
          `DV_CHECK_FATAL(cfg.ecc_data_agent_cfgs[i].is_active);
          virtual_sequencer.ecc_data_sequencers[i] = ecc_data_agents[i].sequencer;
        end
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
