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

  // This extends a function from dv_base_test which allows us to pass handles to a sequence
  extern virtual function void configure_sequence(uvm_sequence seq);
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

function void rom_ctrl_base_test::configure_sequence(uvm_sequence seq);
  rom_ctrl_base_vseq vseq;

  if (!$cast(vseq, seq)) begin
    `uvm_fatal("unknown_sequence", "Cannot cast seq to a rom_ctrl_base_vseq.")
  end

  super.configure_sequence(seq);

  // If we have been configured to skip the middle of the initial ROM read, give the vseq the
  // sequencer that controls the driver that can do so.
  if (cfg.get_skip_middle()) begin
    vseq.m_addr_force_sequencer = env.get_addr_force_sequencer();
  end
endfunction
