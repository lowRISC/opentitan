// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class riscv_jtag_sba_test extends uvm_test;

  `uvm_component_utils(riscv_jtag_sba_test)

  dm_env             env;
  rjtag_dmi_sequence seq;

  function new(string name = "riscv_jtag_sba_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    env = dm_env::type_id::create("env", this);
    seq = rjtag_dmi_sequence::type_id::create("seq");
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    seq.start(env.m_agt.m_seqr);
    phase.drop_objection(this);
  endtask : run_phase

endclass : riscv_jtag_sba_test
