// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_env #(type CFG_T               = cip_base_env_cfg,
                     type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer,
                     type SCOREBOARD_T        = cip_base_scoreboard,
                     type COV_T               = cip_base_env_cov)
                     extends dv_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T);

  `uvm_component_param_utils(cip_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T))

  tl_agent                    m_tl_agent;
  tl_reg_adapter              m_tl_reg_adapter;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.zero_delays) begin
      cfg.m_tl_agent_cfg.a_valid_delay_min = 0;
      cfg.m_tl_agent_cfg.a_valid_delay_max = 0;
      cfg.m_tl_agent_cfg.d_valid_delay_min = 0;
      cfg.m_tl_agent_cfg.d_valid_delay_max = 0;
      cfg.m_tl_agent_cfg.a_ready_delay_min = 0;
      cfg.m_tl_agent_cfg.a_ready_delay_max = 0;
      cfg.m_tl_agent_cfg.d_ready_delay_min = 0;
      cfg.m_tl_agent_cfg.d_ready_delay_max = 0;
    end

    // get vifs
    if (!uvm_config_db#(intr_vif)::get(this, "", "intr_vif", cfg.intr_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get intr_vif from uvm_config_db")
    end
    if (!uvm_config_db#(alerts_vif)::get(this, "", "alerts_vif", cfg.alerts_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get alerts_vif from uvm_config_db")
    end
    if (!uvm_config_db#(devmode_vif)::get(this, "", "devmode_vif", cfg.devmode_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get devmode_vif from uvm_config_db")
    end
    if (!uvm_config_db#(tlul_assert_vif)::get(this, "", "tlul_assert_vif",
                                              cfg.tlul_assert_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get tlul_assert_vif from uvm_config_db")
    end

    // create components
    m_tl_agent = tl_agent::type_id::create("m_tl_agent", this);
    m_tl_reg_adapter = tl_reg_adapter#()::type_id::create("m_tl_reg_adapter");
    uvm_config_db#(tl_agent_cfg)::set(this, "m_tl_agent*", "cfg", cfg.m_tl_agent_cfg);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_tl_agent.mon.a_chan_port.connect(scoreboard.tl_a_chan_fifo.analysis_export);
      m_tl_agent.mon.d_chan_port.connect(scoreboard.tl_d_chan_fifo.analysis_export);
    end
    if (cfg.is_active) begin
      virtual_sequencer.tl_sequencer_h = m_tl_agent.seqr;
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // Set the TL adapter / sequencer to the default_map.
    cfg.ral.default_map.set_sequencer(m_tl_agent.seqr, m_tl_reg_adapter);
  endfunction : end_of_elaboration_phase

endclass

