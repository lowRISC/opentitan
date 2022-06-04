// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_agent extends dv_base_agent #(
  .CFG_T      (jtag_riscv_agent_cfg),
  .SEQUENCER_T(jtag_riscv_sequencer),
  .DRIVER_T   (jtag_riscv_driver),
  .MONITOR_T  (jtag_riscv_monitor),
  .COV_T      (jtag_riscv_agent_cov)
);

  `uvm_component_utils(jtag_riscv_agent)
  `uvm_component_new

  jtag_agent m_jtag_agent;

  // This jtag_riscv_agent is a high level agent that utilizes jtag_agent sequences to perform
  // specific combination of sequences for RISCV jtag.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // In dmi mode, jtag_agent_cfg has to be created at
    // *_env_cfg.initialize().
    // So mask these two lines when jtag_dmi is enabled and
    // get cfg from *_env_cfg.initialize()
    if (cfg.use_jtag_dmi == 0) begin
      cfg.m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
      `DV_CHECK_RANDOMIZE_FATAL(cfg.m_jtag_agent_cfg)
    end
    m_jtag_agent = jtag_agent::type_id::create("m_jtag_agent", this);
    uvm_config_db#(jtag_agent_cfg)::set(this, "m_jtag_agent", "cfg", cfg.m_jtag_agent_cfg);
    cfg.m_jtag_agent_cfg.en_cov = cfg.en_cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    sequencer.jtag_sequencer_h = m_jtag_agent.sequencer;
    cfg.jtag_sequencer_h       = m_jtag_agent.sequencer;
    if (cfg.use_jtag_dmi == 0) begin
      m_jtag_agent.monitor.analysis_port.connect(monitor.jtag_item_fifo.analysis_export);
    end
  endfunction

endclass
