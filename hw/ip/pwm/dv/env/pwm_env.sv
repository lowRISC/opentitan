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

  pwm_monitor#(PWM_NUM_CHANNELS) m_pwm_monitor;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // instantiate pwm_monitor
    m_pwm_monitor = pwm_monitor#(PWM_NUM_CHANNELS)::type_id::create("m_pwm_monitor", this);
    m_pwm_monitor.cfg = cfg.m_pwm_monitor_cfg;

    // generate core clock (must slower than bus clock)
    if (!uvm_config_db#(virtual clk_rst_if)
        ::get(this, "", "clk_rst_core_vif", cfg.clk_rst_core_vif)) begin
      `uvm_fatal(`gfn, "\n  pwm_env: failed to get clk_rst_core_vif from uvm_config_db")
    end
    cfg.core_clk_freq_mhz = cfg.get_clk_core_freq();
    cfg.clk_rst_core_vif.set_freq_mhz(cfg.core_clk_freq_mhz);
    `uvm_info(`gfn, $sformatf("\n  env_cfg: bus_clk %0d Mhz, core_clk %0d Mhz",
        cfg.clk_rst_vif.clk_freq_mhz, cfg.clk_rst_core_vif.clk_freq_mhz), UVM_DEBUG)
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
