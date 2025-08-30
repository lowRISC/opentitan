// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_env extends cip_base_env #(
    .CFG_T              (mbx_env_cfg),
    .COV_T              (mbx_env_cov),
    .VIRTUAL_SEQUENCER_T(mbx_virtual_sequencer),
    .SCOREBOARD_T       (mbx_scoreboard)
  );

  `uvm_component_utils(mbx_env)

  `uvm_component_new

  // TL Agent to model the Mailbox SRAM.
  tl_agent m_tl_agent_sram;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(intr_vif)::get(this, "", "intr_soc_vif", cfg.intr_soc_vif) &&
        cfg.num_interrupts > 0) begin
      `uvm_fatal(get_full_name(), "failed to get intr_soc_vif from uvm_config_db")
    end

    // SRAM TL agent.
    m_tl_agent_sram = tl_agent::type_id::create("m_tl_agent_sram", this);
    uvm_config_db#(tl_agent_cfg)::set(this, "m_tl_agent_sram", "cfg", cfg.m_tl_agent_sram_cfg);

    cfg.m_tl_agent_sram_cfg.synchronise_ports = 1'b1;

  endfunction: build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    virtual_sequencer.tl_sequencer_sram_h = m_tl_agent_sram.sequencer;

    // Connect tl_agent monitor ports to scoreboard analysis FIFOs.
    m_tl_agent_sram.monitor.a_chan_port.connect(
        scoreboard.tl_a_chan_fifos["tl_sram_a_chan"].analysis_export);
    m_tl_agent_sram.monitor.d_chan_port.connect(
        scoreboard.tl_d_chan_fifos["tl_sram_d_chan"].analysis_export);
    m_tl_agent_sram.monitor.channel_dir_port.connect(
        scoreboard.tl_dir_fifos["tl_sram_dir"].analysis_export);
  endfunction: connect_phase

endclass: mbx_env
