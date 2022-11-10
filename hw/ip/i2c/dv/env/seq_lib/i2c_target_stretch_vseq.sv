// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_stretch_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stretch_vseq)
  `uvm_object_new

  bit wr_end = 0;

  constraint num_trans_c { num_trans inside {[1 : 5]}; }

  virtual task body();
    `uvm_info(`gfn, $sformatf("num_trans:%0d", num_trans), UVM_MEDIUM)

    cfg.min_data = 100;
    cfg.max_data = 200;
    cfg.m_i2c_agent_cfg.use_seq_term = 1;
    do_clear_all_interrupts = 0;

    super.body();
  endtask // body

  task process_acq();
    process_slow_acq();
    wr_end = 1;
  endtask

  task process_txq();
    process_slow_txq();
    wait (wr_end == 1);
    cfg.m_i2c_agent_cfg.use_seq_term = 0;
  endtask

endclass // i2c_target_stretch_vseq
