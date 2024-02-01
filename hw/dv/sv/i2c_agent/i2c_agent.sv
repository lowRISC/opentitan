// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent extends dv_base_agent #(
      .CFG_T           (i2c_agent_cfg),
      .DRIVER_T        (i2c_driver),
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
    cfg.has_req_fifo = 1;
  endfunction : build_phase

endclass
