// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_base_test extends cip_base_test #(.CFG_T(racl_ctrl_env_cfg),
                                                  .ENV_T(racl_ctrl_env));

  `uvm_component_utils(racl_ctrl_base_test)

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);

  // Configure the given sequence, installing sequencers for the error log agents. This test can
  // only run (virtual) sequences that derive from racl_ctrl_base_vseq.
  //
  // Overridden from dv_base_test
  extern function void configure_sequence(uvm_sequence seq);
endclass

function racl_ctrl_base_test::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void racl_ctrl_base_test::build_phase(uvm_phase phase);
  dv_base_reg_pkg::dv_base_reg_block blk;

  super.build_phase(phase);

  // Configure the environment config to enable auto-prediction in the system register map for the
  // register model. This means that the scoreboard in the environment will not need to manually
  // call predict.
  blk = cfg.ral_models[racl_ctrl_ral_pkg::racl_ctrl_reg_block::type_name];
  blk.default_map.get_root_map().set_auto_predict();
endfunction

function void racl_ctrl_base_test::configure_sequence(uvm_sequence seq);
  racl_ctrl_base_vseq seq_;
  `downcast(seq_, seq)

  super.configure_sequence(seq);

  seq_.internal_error_log_sequencer_h = env.internal_error_agent.sequencer;
  seq_.external_error_log_sequencer_h = env.external_error_agent.sequencer;
endfunction
