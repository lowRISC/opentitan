// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_env extends cip_base_env #(.CFG_T              (racl_ctrl_env_cfg),
                                           .COV_T              (racl_ctrl_env_cov),
                                           .VIRTUAL_SEQUENCER_T(racl_ctrl_virtual_sequencer),
                                           .SCOREBOARD_T       (racl_ctrl_scoreboard));
  `uvm_component_utils(racl_ctrl_env)

  // Agents to drive the racl_error_i and racl_error_external_i input ports
  racl_error_log_agent internal_error_agent;
  racl_error_log_agent external_error_agent;

  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
endclass

function racl_ctrl_env::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

function void racl_ctrl_env::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (!uvm_config_db#(int unsigned)::get(null, "*.env",
                                         "num_subscribing_ips",
                                         cfg.internal_error_agent_cfg.num_subscribing_ips)) begin
    `uvm_info(`gfn, "No num_subscribing_ips value in config db. Default to zero.", UVM_LOW)
  end

  if (!uvm_config_db#(int unsigned)::get(null, "*.env",
                                         "num_external_subscribing_ips",
                                         cfg.external_error_agent_cfg.num_subscribing_ips)) begin
    `uvm_info(`gfn, "No num_external_subscribing_ips value in config db. Default to zero.", UVM_LOW)
  end

  internal_error_agent = racl_error_log_agent::type_id::create("internal_error_agent", this);
  uvm_config_db#(racl_error_log_agent_cfg)::set(this, "internal_error_agent*", "cfg",
                                                cfg.internal_error_agent_cfg);

  external_error_agent = racl_error_log_agent::type_id::create("external_error_agent", this);
  uvm_config_db#(racl_error_log_agent_cfg)::set(this, "external_error_agent*", "cfg",
                                                cfg.external_error_agent_cfg);

  if (!uvm_config_db#(virtual racl_ctrl_policies_if)::get(null, "*.env",
                                                          "policies_if", cfg.policies_vif)) begin
    `uvm_fatal(`gfn, "failed to get policies_if handle from config db")
  end
endfunction
