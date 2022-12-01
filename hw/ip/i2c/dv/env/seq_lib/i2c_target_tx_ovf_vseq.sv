// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// tx_overflow test
class i2c_target_tx_ovf_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_tx_ovf_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.rd_pct = 3;
    cfg.wr_pct = 1;
    cfg.min_data = 100;
    cfg.max_data = 200;
    expected_intr[TxOverflow] = 1;
    cfg.use_drooling_tx = 1;
    num_trans = 5;
  endtask
endclass : i2c_target_tx_ovf_vseq
