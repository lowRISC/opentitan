// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_env extends cip_base_env #(
    .CFG_T              (ac_range_check_env_cfg),
    .COV_T              (ac_range_check_env_cov),
    .VIRTUAL_SEQUENCER_T(ac_range_check_virtual_sequencer),
    .SCOREBOARD_T       (ac_range_check_scoreboard)
  );
  `uvm_component_utils(ac_range_check_env)

  tl_agent tl_csr_agent;
  tl_agent tl_unfilt_agent;
  tl_agent tl_filt_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create CSR TL agent
    tl_csr_agent = tl_agent::type_id::create("tl_csr_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "tl_csr_agent*", "cfg", cfg.tl_csr_agent_cfg);
    cfg.tl_csr_agent_cfg.en_cov = cfg.en_cov;

    // Create Unfiltered TL agent
    tl_unfilt_agent = tl_agent::type_id::create("tl_unfilt_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "tl_unfilt_agent*", "cfg", cfg.tl_unfilt_agent_cfg);
    cfg.tl_unfilt_agent_cfg.en_cov = cfg.en_cov;

    // Create Fltered TL agent
    tl_filt_agent = tl_agent::type_id::create("tl_filt_agent", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "tl_filt_agent*", "cfg", cfg.tl_filt_agent_cfg);
    cfg.tl_filt_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      tl_csr_agent.monitor.analysis_port.connect(scoreboard.tl_csr_fifo.analysis_export);
      tl_unfilt_agent.monitor.analysis_port.connect(scoreboard.tl_unfilt_fifo.analysis_export);
      tl_filt_agent.monitor.analysis_port.connect(scoreboard.tl_filt_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.tl_csr_agent_cfg.is_active) begin
      virtual_sequencer.tl_csr_sqr = tl_csr_agent.sequencer;
    end
    if (cfg.is_active && cfg.tl_unfilt_agent_cfg.is_active) begin
      virtual_sequencer.tl_unfilt_sqr = tl_unfilt_agent.sequencer;
    end
    if (cfg.is_active && cfg.tl_filt_agent_cfg.is_active) begin
      virtual_sequencer.tl_filt_sqr = tl_filt_agent.sequencer;
    end
  endfunction

endclass
