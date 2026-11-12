// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_test extends cip_base_test #(
    .CFG_T(rram_ctrl_env_cfg),
    .ENV_T(rram_ctrl_env)
  );

  `uvm_component_utils(rram_ctrl_base_test)

  extern function new(string name="", uvm_component parent=null);
  extern task run_phase(uvm_phase phase);
endclass : rram_ctrl_base_test

function rram_ctrl_base_test::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

task rram_ctrl_base_test::run_phase(uvm_phase phase);
  // Randomise the contents of the RRAM memory through the backdoor
  env.m_data_bkdr_util.randomize_mem();
  env.m_info_bkdr_util.randomize_mem();

  fork
    super.run_phase(phase);
    env.m_key_agent.run_device_seq();
  join
endtask
