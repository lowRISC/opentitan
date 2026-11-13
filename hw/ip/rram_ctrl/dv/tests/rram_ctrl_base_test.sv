// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_test extends cip_base_test #(
    .CFG_T(rram_ctrl_env_cfg),
    .ENV_T(rram_ctrl_env)
  );

  `uvm_component_utils(rram_ctrl_base_test)

  // The base class dv_base_test creates the following instances:
  //   - rram_ctrl_env_cfg: cfg
  //   - rram_ctrl_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in the run_phase.
  // As such, nothing more needs to be done

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);

  // Gives the vseq the sequencers it needs. This function is declared in dv_base_test.
  extern virtual function void configure_sequence(uvm_sequence seq);

endclass : rram_ctrl_base_test


function rram_ctrl_base_test::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_base_test::configure_sequence(uvm_sequence seq);
  rram_ctrl_base_vseq vseq;

  if (!$cast(vseq, seq)) begin
    `uvm_fatal("unknown_sequence", "Cannot cast seq to a rram_ctrl_base_vseq.")
  end

  super.configure_sequence(seq);
  vseq.m_otp_macro_sequencer = env.get_otp_macro_sequencer();
endfunction : configure_sequence
