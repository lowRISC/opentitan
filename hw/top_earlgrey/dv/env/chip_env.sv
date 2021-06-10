// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_env extends cip_base_env #(
    .CFG_T              (chip_env_cfg),
    .COV_T              (chip_env_cov),
    .VIRTUAL_SEQUENCER_T(chip_virtual_sequencer),
    .SCOREBOARD_T       (chip_scoreboard)
  );
  `uvm_component_utils(chip_env)

  uart_agent          m_uart_agent;
  jtag_agent          m_jtag_agent;
  spi_agent           m_spi_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // configure the cpu d tl agent
    // get the vifs from config db
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", cfg.gpio_vif)) begin
      `uvm_fatal(`gfn, "failed to get gpio_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual pins_if#(2))::get(this, "", "tap_straps_vif",
        cfg.tap_straps_vif)) begin
      `uvm_fatal(`gfn, "failed to get tap_straps_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual pins_if#(2))::get(this, "", "dft_straps_vif",
        cfg.dft_straps_vif)) begin
      `uvm_fatal(`gfn, "failed to get dft_straps_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual pins_if#(3))::get(this, "", "sw_straps_vif",
        cfg.sw_straps_vif)) begin
      `uvm_fatal(`gfn, "failed to get sw_straps_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual pins_if#(1))::get(this, "", "rst_n_mon_vif",
        cfg.rst_n_mon_vif)) begin
      `uvm_fatal(`gfn, "failed to get rst_n_mon_vif from uvm_config_db")
    end

    for (chip_mem_e mem = mem.first(), int i = 0; i < mem.num(); mem = mem.next(), i++) begin
      if (!uvm_config_db#(mem_bkdr_util)::get(
          this, "", $sformatf("mem_bkdr_util[%0s]", mem.name()), cfg.mem_bkdr_util_h[mem])) begin
        `uvm_fatal(`gfn, $sformatf("failed to get mem_bkdr_util[%0s] from uvm_config_db", mem))
      end
    end

    // get the handle to the sw log monitor for available sw_images.
    if (!uvm_config_db#(sw_logger_vif)::get(this, "", "sw_logger_vif", cfg.sw_logger_vif)) begin
      `uvm_fatal(`gfn, "failed to get sw_logger_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual sw_test_status_if)::get(this, "", "sw_test_status_vif",
        cfg.sw_test_status_vif)) begin
      `uvm_fatal(`gfn, "failed to get sw_test_status_vif from uvm_config_db")
    end

    // create components
    m_uart_agent = uart_agent::type_id::create("m_uart_agent", this);
    uvm_config_db#(uart_agent_cfg)::set(this, "m_uart_agent*", "cfg", cfg.m_uart_agent_cfg);

    m_jtag_agent = jtag_agent::type_id::create("m_jtag_agent", this);
    uvm_config_db#(jtag_agent_cfg)::set(this, "m_jtag_agent*", "cfg", cfg.m_jtag_agent_cfg);

    m_spi_agent = spi_agent::type_id::create("m_spi_agent", this);
    uvm_config_db#(spi_agent_cfg)::set(this, "m_spi_agent*", "cfg", cfg.m_spi_agent_cfg);

    // disable alert_esc_agent's driver and only use its monitor
    foreach (LIST_OF_ALERTS[i]) begin
      cfg.m_alert_agent_cfg[LIST_OF_ALERTS[i]].is_active = 0;
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_uart_agent.monitor.tx_analysis_port.connect(scoreboard.uart_tx_fifo.analysis_export);
      m_uart_agent.monitor.rx_analysis_port.connect(scoreboard.uart_rx_fifo.analysis_export);
      m_jtag_agent.monitor.analysis_port.connect(scoreboard.jtag_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.m_uart_agent_cfg.is_active) begin
      virtual_sequencer.uart_sequencer_h = m_uart_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_jtag_agent_cfg.is_active) begin
      virtual_sequencer.jtag_sequencer_h = m_jtag_agent.sequencer;
    end
    if (cfg.is_active && cfg.m_spi_agent_cfg.is_active) begin
      virtual_sequencer.spi_sequencer_h = m_spi_agent.sequencer;
    end

    // Connect the DUT's UART TX TLM port to the sequencer.
    m_uart_agent.monitor.tx_analysis_port.connect(virtual_sequencer.uart_tx_fifo.analysis_export);
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
  endfunction

endclass
