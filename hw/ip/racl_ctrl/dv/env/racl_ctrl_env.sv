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

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass

function racl_ctrl_env::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void racl_ctrl_env::build_phase(uvm_phase phase);
  racl_ctrl_env_wrapper_cfg wrapper;

  super.build_phase(phase);

  // Consume the configuration for the environment from uvm_config_db
  if (!uvm_config_db#(racl_ctrl_env_wrapper_cfg)::get(null, "*.env", "wrapper", wrapper)) begin
    `uvm_fatal(`gfn, "Cannot find wrapper object in config db")
  end
  cfg.internal_error_agent_cfg.num_subscribing_ips = wrapper.num_subscribing_ips;
  cfg.external_error_agent_cfg.num_subscribing_ips = wrapper.num_external_subscribing_ips;

  cfg.policies_vif                 = wrapper.policies_vif;
  cfg.internal_error_agent_cfg.vif = wrapper.internal_error_vif;
  cfg.external_error_agent_cfg.vif = wrapper.external_error_vif;

  // Connect up configuration for each of the agents in uvm_config_db
  uvm_config_db#(racl_error_log_agent_cfg)::set(this, "internal_error_agent*", "cfg",
                                                cfg.internal_error_agent_cfg);
  uvm_config_db#(racl_error_log_agent_cfg)::set(this, "external_error_agent*", "cfg",
                                                cfg.external_error_agent_cfg);

  // Create tha agents
  internal_error_agent = racl_error_log_agent::type_id::create("internal_error_agent", this);
  external_error_agent = racl_error_log_agent::type_id::create("external_error_agent", this);
endfunction

function void racl_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  internal_error_agent.errors_seen.connect(scoreboard.internal_errors_export);
  external_error_agent.errors_seen.connect(scoreboard.external_errors_export);
endfunction
