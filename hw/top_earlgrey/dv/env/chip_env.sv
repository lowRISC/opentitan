// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_env extends dv_base_env #(
    .CFG_T              (chip_env_cfg),
    .COV_T              (chip_env_cov),
    .VIRTUAL_SEQUENCER_T(chip_virtual_sequencer),
    .SCOREBOARD_T       (chip_scoreboard)
  );
  `uvm_component_utils(chip_env)

  uart_agent          m_uart_agent;
  jtag_agent          m_jtag_agent;
  tl_agent            m_cpu_d_tl_agent;
  chip_tl_reg_adapter m_cpu_d_tl_reg_adapter;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // configure the cpu d tl agent
    if (cfg.m_cpu_d_tl_agent_cfg.is_active && cfg.zero_delays) begin
      cfg.m_cpu_d_tl_agent_cfg.a_valid_delay_min = 0;
      cfg.m_cpu_d_tl_agent_cfg.a_valid_delay_max = 0;
      cfg.m_cpu_d_tl_agent_cfg.d_valid_delay_min = 0;
      cfg.m_cpu_d_tl_agent_cfg.d_valid_delay_max = 0;
      cfg.m_cpu_d_tl_agent_cfg.a_ready_delay_min = 0;
      cfg.m_cpu_d_tl_agent_cfg.a_ready_delay_max = 0;
      cfg.m_cpu_d_tl_agent_cfg.d_ready_delay_min = 0;
      cfg.m_cpu_d_tl_agent_cfg.d_ready_delay_max = 0;
    end

    // get the vifs from config db
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", cfg.gpio_vif)) begin
      `uvm_fatal(`gfn, "failed to get gpio_vif from uvm_config_db")
    end

    foreach (cfg.mem_bkdr_vifs[mem]) begin
      if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", $sformatf("mem_bkdr_vifs[%0s]", mem.name),
                                             cfg.mem_bkdr_vifs[mem])) begin
        `uvm_fatal(`gfn, $sformatf("failed to get mem_bkdr_vifs[%0s] from uvm_config_db", mem.name))
      end
    end

    if (!uvm_config_db#(sw_msg_monitor_vif)::get(this, "", "sw_msg_monitor_vif",
                                                 cfg.sw_msg_monitor_vif)) begin
      `uvm_fatal(`gfn, "failed to get sw_msg_monitor_vif from uvm_config_db")
    end

    // create components
    m_uart_agent = uart_agent::type_id::create("m_uart_agent", this);
    uvm_config_db#(uart_agent_cfg)::set(this, "m_uart_agent*", "cfg", cfg.m_uart_agent_cfg);
    m_jtag_agent = jtag_agent::type_id::create("m_jtag_agent", this);
    uvm_config_db#(jtag_agent_cfg)::set(this, "m_jtag_agent*", "cfg", cfg.m_jtag_agent_cfg);
    m_cpu_d_tl_agent = tl_agent::type_id::create("m_cpu_d_tl_agent", this);
    m_cpu_d_tl_reg_adapter = chip_tl_reg_adapter::type_id::create("m_cpu_d_tl_reg_adapter");
    uvm_config_db#(tl_agent_cfg)::set(this, "m_cpu_d_tl_agent*", "cfg", cfg.m_cpu_d_tl_agent_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_uart_agent.monitor.tx_analysis_port.connect(scoreboard.uart_tx_fifo.analysis_export);
      m_uart_agent.monitor.rx_analysis_port.connect(scoreboard.uart_rx_fifo.analysis_export);
      m_jtag_agent.monitor.analysis_port.connect(scoreboard.jtag_fifo.analysis_export);
      // TODO: add scoreboard connections for monitoring tl accesses
      // m_cpu_d_tl_agent.mon.a_chan_port.connect(scoreboard.tl_a_chan_fifo.analysis_export);
      // m_cpu_d_tl_agent.mon.d_chan_port.connect(scoreboard.tl_d_chan_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_uart_agent_cfg.is_active) begin
      virtual_sequencer.uart_sequencer_h = m_uart_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_jtag_agent_cfg.is_active) begin
      virtual_sequencer.jtag_sequencer_h = m_jtag_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_cpu_d_tl_agent_cfg.is_active) begin
      virtual_sequencer.cpu_d_tl_sequencer_h = m_cpu_d_tl_agent.sequencer;
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (cfg.stub_cpu) begin
      // Set the TL adapter / sequencer to the default_map.
      cfg.ral.default_map.set_sequencer(m_cpu_d_tl_agent.sequencer, m_cpu_d_tl_reg_adapter);
    end
  endfunction : end_of_elaboration_phase

endclass
