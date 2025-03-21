// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_env extends cip_base_env #(.CFG_T              (racl_ctrl_env_cfg),
                                           .COV_T              (racl_ctrl_env_cov),
                                           .VIRTUAL_SEQUENCER_T(racl_ctrl_virtual_sequencer),
                                           .SCOREBOARD_T       (racl_ctrl_scoreboard));
  `uvm_component_utils(racl_ctrl_env)

  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
endclass

function racl_ctrl_env::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

function void racl_ctrl_env::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (!uvm_config_db#(virtual racl_ctrl_policies_if)::get(null, "*.env",
                                                          "policies_if", cfg.policies_vif))
    `uvm_fatal(`gfn, "failed to get policies_if handle from config db")
endfunction
