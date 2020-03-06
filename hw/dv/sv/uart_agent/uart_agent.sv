// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_agent extends dv_base_agent#(
    .CFG_T          (uart_agent_cfg),
    .DRIVER_T       (uart_driver),
    .SEQUENCER_T    (uart_sequencer),
    .MONITOR_T      (uart_monitor),
    .COV_T          (uart_agent_cov)
  );
  `uvm_component_utils(uart_agent)

  uart_logger m_logger;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get uart_if handle
    if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get uart_if handle from uvm_config_db")
    end

    // Create the logger instance.
    if (cfg.en_logger) begin
      m_logger = uart_logger::type_id::create("m_logger", this);
      m_logger.cfg = cfg;
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect the logger TLM port to the monitor.
    if (cfg.en_logger) begin
      if (cfg.use_rx_for_logger) begin
        monitor.rx_analysis_port.connect(m_logger.log_item_fifo.analysis_export);
      end else begin
        monitor.tx_analysis_port.connect(m_logger.log_item_fifo.analysis_export);
      end
    end
  endfunction

endclass
