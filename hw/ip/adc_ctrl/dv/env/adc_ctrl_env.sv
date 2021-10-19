// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_env extends cip_base_env #(
  .CFG_T              (adc_ctrl_env_cfg),
  .COV_T              (adc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(adc_ctrl_virtual_sequencer),
  .SCOREBOARD_T       (adc_ctrl_scoreboard)
);

  adc_push_pull_agent_t m_adc_push_pull_agent[ADC_CTRL_CHANNELS];

  `uvm_component_utils(adc_ctrl_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // get the vifs from config db
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "clk_aon_rst_vif", cfg.clk_aon_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get clk_aon_rst_vif from uvm_config_db")
    end

    for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      string name = $sformatf("m_adc_push_pull_agent_%0d", idx);
      m_adc_push_pull_agent[idx] = adc_push_pull_agent_t::type_id::create(name, this);
      uvm_config_db#(adc_push_pull_config_t)::set(this, name, "cfg", cfg.m_adc_push_pull_cfg[idx]);
    end

    if (!uvm_config_db#(wakeup_vif_t)::get(this, "", "wakeup_vif", cfg.wakeup_vif)) begin
      `uvm_fatal(`gfn, "failed to get wakeup_vif from uvm_config_db")
    end

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect ADC push pull agent monitors to scoreboard
    for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      m_adc_push_pull_agent[idx].monitor.analysis_port.connect(
          scoreboard.m_adc_push_pull_fifo[idx].analysis_export);
    end
  endfunction

endclass
