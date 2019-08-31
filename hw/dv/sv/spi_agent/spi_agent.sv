// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_agent extends uvm_agent;
  `uvm_component_utils(spi_agent)

  spi_agent_cfg  cfg;
  spi_driver     driver;
  spi_sequencer  sequencer;
  spi_monitor    monitor;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get spi_agent_cfg object from uvm_config_db
    if (!uvm_config_db#(spi_agent_cfg)::get(this, "", "cfg", cfg))
      `uvm_fatal(`gfn, "failed to get spi_agent_cfg object from uvm_config_db")

    // get spi_if handle
    if (!uvm_config_db#(virtual spi_if)::get(this, "", "vif", cfg.vif))
      `uvm_fatal(`gfn, "failed to get spi_if handle from uvm_config_db")

    // create components
    monitor = spi_monitor::type_id::create("monitor", this);
    monitor.cfg = cfg;
    if (cfg.is_active) begin
      sequencer = spi_sequencer::type_id::create("sequencer", this);
      sequencer.cfg = cfg;
      if (cfg.mode == Host) begin
        driver = spi_host_driver::type_id::create("driver", this);
      end else begin
        driver = spi_device_driver::type_id::create("driver", this);
      end
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
