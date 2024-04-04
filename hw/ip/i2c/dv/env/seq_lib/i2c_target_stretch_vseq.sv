// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_stretch_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stretch_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[1 : 5]}; }

  virtual task pre_start();
    super.pre_start();
    cfg.min_data = 100;
    cfg.max_data = 200;
    cfg.slow_acq = 1;
    cfg.slow_txq = 1;
  endtask
endclass // i2c_target_stretch_vseq
