// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_stress_wr_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stress_wr_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[1 : 5]}; }

  virtual task pre_start();
    super.pre_start();
    cfg.min_data = 80;
    cfg.max_data = 200;
    cfg.rd_pct = 0;
    cfg.slow_acq = 1;
  endtask
endclass
