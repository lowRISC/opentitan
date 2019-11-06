// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink agent
// ---------------------------------------------
class tl_agent extends uvm_agent;

  tl_host_driver     host_driver;
  tl_device_driver   device_driver;
  tl_monitor         mon;
  tl_sequencer       seqr;
  tl_agent_cfg       cfg;
  tl_agent_cov       cov;

  `uvm_component_utils(tl_agent)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(tl_agent_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal("NO_CFG", {"cfg must be set for:", get_full_name(), ".cfg"});
    end
    if (cfg.is_active && get_is_active() == UVM_ACTIVE) begin
      if (cfg.is_host) begin
        host_driver = tl_host_driver::type_id::create("host_driver", this);
      end else begin
        device_driver = tl_device_driver::type_id::create("device_driver", this);
      end
      seqr = tl_sequencer::type_id::create("seqr", this);
      seqr.cfg = cfg;
    end
    mon = tl_monitor::type_id::create("mon", this);
    if (cfg.en_cov) begin
      cov = tl_agent_cov ::type_id::create("cov", this);
      cov.cfg = cfg;
    end
    mon.cov = cov;
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    if (cfg.is_active && get_is_active() == UVM_ACTIVE) begin
      if (cfg.is_host) begin
        host_driver.seq_item_port.connect(seqr.seq_item_export);
      end else begin
        device_driver.seq_item_port.connect(seqr.seq_item_export);
        mon.a_chan_port.connect(seqr.a_chan_req_fifo.analysis_export);
      end
    end
  endfunction : connect_phase

endclass : tl_agent
