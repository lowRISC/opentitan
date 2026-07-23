// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_base_test extends cip_base_test #(
    .CFG_T(rom_ctrl_env_cfg),
    .ENV_T(rom_ctrl_env)
  );

  `uvm_component_utils(rom_ctrl_base_test)

  extern function new (string name, uvm_component parent);
  extern virtual task run_phase (uvm_phase phase);
endclass : rom_ctrl_base_test

function rom_ctrl_base_test::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task rom_ctrl_base_test::run_phase (uvm_phase phase);
  // Run a sequence in m_kmac_agent that will respond with to requests with digests
  //
  // This gets run in the background: it will run forever and we want to be able to finish the test
  // when the rest of run_phase completes.
  fork
    env.m_kmac_agent.run_device_seq();
  join_none

  super.run_phase(phase);
endtask
