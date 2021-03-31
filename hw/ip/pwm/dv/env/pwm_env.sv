// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_env extends cip_base_env #(
    .CFG_T              (pwm_env_cfg),
    .COV_T              (pwm_env_cov),
    .VIRTUAL_SEQUENCER_T(pwm_virtual_sequencer),
    .SCOREBOARD_T       (pwm_scoreboard)
  );
  `uvm_component_utils(pwm_env)
  `uvm_component_new

  pwm_monitor m_pwm_monitor;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // instantiate pwm_monitor
    m_pwm_monitor = pwm_monitor::type_id::create("m_pwm_monitor", this);
    m_pwm_monitor.cfg = cfg;
    m_pwm_monitor.cov = cov;
    // get vif handle
    if (!uvm_config_db#(virtual pwm_if#(PWM_NUM_CHANNELS))::
        get(this, "", "pwm_vif", cfg.pwm_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get pwm_vif from uvm_config_db")
    end

    // generate core clock (must slower than bus clock)
    if (!uvm_config_db#(virtual clk_rst_if)::
        get(this, "", "clk_rst_core_vif", cfg.clk_rst_core_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get clk_rst_core_vif from uvm_config_db")
    end
    cfg.core_clk_freq_mhz = cfg.get_clk_core_freq(cfg.seq_cfg.pwm_core_clk_ratio);
    cfg.clk_rst_core_vif.set_freq_mhz(cfg.core_clk_freq_mhz);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
        m_pwm_monitor.item_port[i].connect(scoreboard.item_fifo[i].analysis_export);
      end
    end
  endfunction : connect_phase

endclass : pwm_env
