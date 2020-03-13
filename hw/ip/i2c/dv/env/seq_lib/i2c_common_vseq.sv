// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_common_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_common_vseq)

  constraint num_trans_c {
    num_trans inside {[10:25]};
  }

  `uvm_object_new

  task pre_start();
    super.pre_start();
  endtask : pre_start

  virtual task body();
    // disable i2c_monitor since it can not handle this test
    `uvm_info(`gtn, $sformatf("disable i2c_monitor"), UVM_DEBUG)
    cfg.m_i2c_agent_cfg.en_monitor <= 1'b0;
    run_common_vseq_wrapper(num_trans); // inherit from cip_base_vseq.sv
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");

    // intr_state is affected by writes to other csrs
    csr_excl.add_excl({scope, ".", "intr_state"}, CsrExclCheck);
    // RO registers - exclude init and write-read check
    csr_excl.add_excl({scope, ".", "status"}, CsrExclWriteCheck);
    csr_excl.add_excl({scope, ".", "fifo_status"}, CsrExclWriteCheck);
    // RO registers - exclude init and write-read check
    csr_excl.add_excl({scope, ".", "val"}, CsrExclCheck);
    csr_excl.add_excl({scope, ".", "rdata"}, CsrExclCheck);
  endfunction : add_csr_exclusions

  task post_start();
    `uvm_info(`gfn, "stop simulation", UVM_DEBUG)
  endtask : post_start

endclass : i2c_common_vseq
