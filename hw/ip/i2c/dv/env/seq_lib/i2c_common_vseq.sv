// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_common_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}

  `uvm_object_new

  task pre_start();
    super.pre_start();
  endtask : pre_start

  virtual task body();
    // disable i2c_monitor since it can not handle this test
    `uvm_info(`gfn, $sformatf("\ndisable i2c_monitor and i2c_scoreboard"), UVM_DEBUG)
    cfg.m_i2c_agent_cfg.en_monitor = 1'b0;
    run_common_vseq_wrapper(num_trans);  // inherit from cip_base_vseq.sv
  endtask : body

  task post_start();
    `uvm_info(`gfn, "\nstop simulation", UVM_DEBUG)
  endtask : post_start

endclass : i2c_common_vseq
