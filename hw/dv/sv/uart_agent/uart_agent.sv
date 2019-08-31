// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_agent extends uvm_agent;
  `uvm_component_utils(uart_agent)

  uart_agent_cfg  cfg;
  uart_driver     driver;
  uart_sequencer  sequencer;
  uart_monitor    monitor;
  uart_agent_cov  cov;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get uart_agent_cfg object from uvm_config_db
    if (!uvm_config_db#(uart_agent_cfg)::get(this, "", "cfg", cfg))
      `uvm_fatal(`gfn, "failed to get uart_agent_cfg object from uvm_config_db")

    // get uart_if handle
    if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", cfg.vif))
      `uvm_fatal(`gfn, "failed to get uart_if handle from uvm_config_db")

    if (cfg.en_cov) begin
      cov = uart_agent_cov ::type_id::create("cov", this);
      cov.cfg = cfg;
    end
    // create components
    monitor = uart_monitor::type_id::create("monitor", this);
    monitor.cfg = cfg;
    monitor.cov = cov;
    if (cfg.is_active) begin
      sequencer = uart_sequencer::type_id::create("sequencer", this);
      sequencer.cfg = cfg;
      driver = uart_driver::type_id::create("driver", this);
      driver.cfg = cfg;
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_active) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

endclass
