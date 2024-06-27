// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_env extends cip_base_env #(
  .CFG_T              (chip_env_cfg),
  .COV_T              (chip_env_cov),
  .VIRTUAL_SEQUENCER_T(chip_virtual_sequencer),
  .SCOREBOARD_T       (chip_scoreboard)
);
  `uvm_component_utils(chip_env)

  uart_agent             m_uart_agents[NUM_UARTS];
  // spi device agents that receive transactions from dut spi host
  spi_agent              m_spi_device_agents[NUM_SPI_HOSTS];
  i2c_agent              m_i2c_agents[NUM_I2CS];
  jtag_riscv_agent       m_jtag_riscv_agent;
  jtag_riscv_reg_adapter m_jtag_riscv_reg_adapter;
  // spi host agent that transmits trasnactions to dut spi device
  spi_agent              m_spi_host_agent;
  pwm_monitor            m_pwm_monitor[NUM_PWM_CHANNELS];
  pattgen_agent          m_pattgen_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // configure the cpu d tl agent
    // get the vifs from config db
    if (!uvm_config_db#(virtual chip_if)::get(this, "", "chip_vif", cfg.chip_vif)) begin
      `uvm_fatal(`gfn, "failed to get chip_vif from uvm_config_db")
    end

    // Set tl_agent's is_active bit based on the stub_cpu value.
    cfg.m_tl_agent_cfg.is_active = cfg.chip_vif.stub_cpu;

    for (chip_mem_e mem = mem.first(), int i = 0; i < mem.num(); mem = mem.next(), i++) begin
      string inst = $sformatf("mem_bkdr_util[%0s]", mem.name());
      bit is_invalid;

      is_invalid = mem inside {[RamMain0:RamMain15]} && (int'(mem - RamMain0) >
                                                         cfg.num_ram_main_tiles - 1);

      is_invalid |= mem inside {[RamRet0:RamRet15]} && (int'(mem - RamRet0) >
                                                        cfg.num_ram_ret_tiles - 1);

      is_invalid |= mem inside {[OtbnDmem0:OtbnDmem15]} && (int'(mem - OtbnDmem0) >
                                                            cfg.num_otbn_dmem_tiles - 1);
      if (is_invalid) continue;
      if (!uvm_config_db#(mem_bkdr_util)::get(this, "", inst, cfg.mem_bkdr_util_h[mem])) begin
        `uvm_fatal(`gfn, {"failed to get ", inst, " from uvm_config_db"})
      end
    end

    // get the handle to the sw log monitor for available sw_images.
    if (!uvm_config_db#(sw_logger_vif)::get(this, "", "sw_logger_vif", cfg.sw_logger_vif)) begin
      `uvm_fatal(`gfn, "failed to get sw_logger_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual sw_test_status_if)::get(
            this, "", "sw_test_status_vif", cfg.sw_test_status_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get sw_test_status_vif from uvm_config_db")
    end

    // get the handle to the ast supply interface.
    if (!uvm_config_db#(virtual ast_supply_if)::get(
            this, "", "ast_supply_vif", cfg.ast_supply_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get ast_supply_vif from uvm_config_db")
    end

    // get the handle to the ast io_ext_clk interface.
    if (!uvm_config_db#(ast_ext_clk_vif)::get(
            this, "", "ast_ext_clk_vif", cfg.ast_ext_clk_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get ast_ext_clk_vif from uvm_config_db")
    end

    // get the handle to the usbdpi clk/rst interface.
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "usbdpi_clk_rst_vif", cfg.usbdpi_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get usbdpi clk_rst_vif from uvm_config_db")
    end

    // get the handle to the usb20 interface.
    if (!uvm_config_db#(usb20_vif)::get(
            this, "", "usb20_vif", cfg.usb20_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get usb20_vif from uvm_config_db")
    end

    // create components
    foreach (m_uart_agents[i]) begin
      m_uart_agents[i] = uart_agent::type_id::create($sformatf("m_uart_agent%0d", i), this);
      uvm_config_db#(uart_agent_cfg)::set(this, $sformatf("m_uart_agent%0d*", i), "cfg",
                                          cfg.m_uart_agent_cfgs[i]);
    end

    // dut spi host, tb spi device
    foreach (m_spi_device_agents[i]) begin
      m_spi_device_agents[i] =
        spi_agent::type_id::create($sformatf("m_spi_device_agents%0d", i), this);
      uvm_config_db#(spi_agent_cfg)::set(this, $sformatf("m_spi_device_agents%0d*", i), "cfg",
                                         cfg.m_spi_device_agent_cfgs[i]);
    end

    foreach (m_i2c_agents[i]) begin
      m_i2c_agents[i] = i2c_agent::type_id::create($sformatf("m_i2c_agent%0d", i), this);
      uvm_config_db#(i2c_agent_cfg)::set(this, $sformatf("m_i2c_agent%0d*", i), "cfg",
                                          cfg.m_i2c_agent_cfgs[i]);
    end

    m_jtag_riscv_agent = jtag_riscv_agent::type_id::create("m_jtag_riscv_agent", this);
    uvm_config_db#(jtag_riscv_agent_cfg)::set(this, "m_jtag_riscv_agent*", "cfg",
                                              cfg.m_jtag_riscv_agent_cfg);

    m_jtag_riscv_reg_adapter = jtag_riscv_reg_adapter::type_id::create(
        "m_jtag_riscv_reg_adapter", null, this.get_full_name()
    );
    m_jtag_riscv_reg_adapter.cfg = cfg.m_jtag_riscv_agent_cfg;

    // dut spi device, tb spi host
    m_spi_host_agent = spi_agent::type_id::create("m_spi_host_agent", this);
    uvm_config_db#(spi_agent_cfg)::set(this, "m_spi_host_agent*", "cfg", cfg.m_spi_host_agent_cfg);

    // instantiate pwm_monitor
    foreach (m_pwm_monitor[i]) begin
      m_pwm_monitor[i] = pwm_monitor::type_id::create($sformatf("m_pwm_monitor%0d", i), this);
      uvm_config_db#(pwm_monitor_cfg)::set(this, $sformatf("m_pwm_monitor%0d*", i), "cfg",
                                           cfg.m_pwm_monitor_cfg[i]);
    end

    // Instantiate pattgen agent
    m_pattgen_agent = pattgen_agent::type_id::create("m_pattgen_agent", this);
    uvm_config_db#(pattgen_agent_cfg)::set(this, "m_pattgen_agent*", "cfg",
                                           cfg.m_pattgen_agent_cfg);

    // disable alert_esc_agent's driver and only use its monitor
    foreach (LIST_OF_ALERTS[i]) begin
      cfg.m_alert_agent_cfgs[LIST_OF_ALERTS[i]].is_active = 0;
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      m_jtag_riscv_agent.monitor.analysis_port.connect(scoreboard.jtag_fifo.analysis_export);
    end
    foreach (m_uart_agents[i]) begin
      if (cfg.is_active && cfg.m_uart_agent_cfgs[i].is_active) begin
        virtual_sequencer.uart_sequencer_hs[i] = m_uart_agents[i].sequencer;
      end
    end

    foreach (m_spi_device_agents[i]) begin
      if (cfg.is_active && cfg.m_spi_device_agent_cfgs[i].is_active) begin
        virtual_sequencer.spi_device_sequencer_hs[i] = m_spi_device_agents[i].sequencer;
      end
    end

    foreach (m_i2c_agents[i]) begin
      virtual_sequencer.i2c_sequencer_hs[i] = m_i2c_agents[i].sequencer;
      // Set default monitor enable to zero for shared io agents.
      cfg.m_i2c_agent_cfgs[i].en_monitor = 1'b0;

      m_i2c_agents[i].monitor.analysis_port.connect(
          virtual_sequencer.i2c_rd_fifos[i].analysis_export);
    end

    if (cfg.is_active && cfg.m_jtag_riscv_agent_cfg.is_active) begin
      virtual_sequencer.jtag_sequencer_h = m_jtag_riscv_agent.sequencer;
    end

    if (cfg.is_active && cfg.m_spi_host_agent_cfg.is_active) begin
      virtual_sequencer.spi_host_sequencer_h = m_spi_host_agent.sequencer;
    end

    // The chip level scoreboard is intentionally kept lightweight, since most tests are directed,
    // with stimulus and checks both contained in the sequence. The following TLM connections from
    // the interface agent's monitor to the sequencer enables sequences to directly retrieve the
    // packets from the monitor for processing / end-to-end checks.

    foreach (m_uart_agents[i]) begin
      m_uart_agents[i].monitor.tx_analysis_port.connect(
          virtual_sequencer.uart_tx_fifos[i].analysis_export);
    end

    foreach (m_pwm_monitor[i]) begin
      m_pwm_monitor[i].analysis_port.connect(virtual_sequencer.pwm_rx_fifo[i].analysis_export);
    end
    for (int i = 0; i < NUM_PATTGEN_CH; i++) begin
      m_pattgen_agent.monitor.item_port[i].connect(
                                          virtual_sequencer.pattgen_rx_fifo[i].analysis_export);
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);

    if (cfg.jtag_riscv_map != null) begin
      cfg.jtag_riscv_map.set_sequencer(m_jtag_riscv_agent.sequencer, m_jtag_riscv_reg_adapter);

      `uvm_info(`gfn, "Setting jtag_riscv_map as default map", UVM_MEDIUM)
      foreach (cfg.ral_models[i]) begin
        cfg.ral_models[i].set_default_map_w_subblks_by_name("jtag_riscv_map");
        `uvm_info(`gfn, cfg.ral_models[i].sprint(), UVM_HIGH)
      end
    end
  endfunction

endclass
