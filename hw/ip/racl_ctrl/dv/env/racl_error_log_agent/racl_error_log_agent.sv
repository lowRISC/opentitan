// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_error_log_agent extends dv_base_agent#(.CFG_T      (racl_error_log_agent_cfg),
                                                  .DRIVER_T   (racl_error_log_driver),
                                                  .SEQUENCER_T(racl_error_log_sequencer),
                                                  .MONITOR_T  (racl_error_log_monitor));
  `uvm_component_utils(racl_error_log_agent)

  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass

function racl_error_log_agent::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

function void racl_error_log_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (!uvm_config_db#(virtual racl_error_log_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(`gfn, "failed to get racl_ctrl_error_log_if handle from uvm_config_db")
  end
endfunction

function void racl_error_log_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  driver.vif = cfg.vif;
  monitor.vif = cfg.vif;
endfunction
