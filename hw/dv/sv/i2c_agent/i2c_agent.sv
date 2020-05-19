// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent extends dv_base_agent #(
      .CFG_T           (i2c_agent_cfg),
      .DRIVER_T        (i2c_driver),
      .HOST_DRIVER_T   (i2c_host_driver),
      .DEVICE_DRIVER_T (i2c_device_driver),
      .SEQUENCER_T     (i2c_sequencer),
      .MONITOR_T       (i2c_monitor),
      .COV_T           (i2c_agent_cov)
  );

  `uvm_component_utils(i2c_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual i2c_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get i2c_if handle from uvm_config_db")
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      monitor.mon_item_port.connect(sequencer.mon_item_fifo.analysis_export);
    end else begin
      `uvm_fatal(`gfn, "failed to connect driver to sequencer")
    end
  endfunction : connect_phase
endclass
