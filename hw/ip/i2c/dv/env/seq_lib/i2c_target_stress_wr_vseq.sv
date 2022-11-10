// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_stress_wr_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stress_wr_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[1 : 5]}; }

  virtual task body();
    `uvm_info(`gfn, $sformatf("num_trans:%0d", num_trans), UVM_MEDIUM)

    cfg.min_data = 80;
    cfg.max_data = 200;
    cfg.rd_pct = 0;
    cfg.m_i2c_agent_cfg.use_seq_term = 1;

    super.body();
  endtask // body

  // slow acq fifo read to create acq_fifo full
  task process_acq();
    process_slow_acq();
    cfg.m_i2c_agent_cfg.use_seq_term = 0;
  endtask
endclass
