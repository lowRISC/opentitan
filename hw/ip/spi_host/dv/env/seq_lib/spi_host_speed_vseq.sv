// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// speed test vseq
class spi_host_speed_vseq extends spi_host_smoke_vseq;
  `uvm_object_utils(spi_host_speed_vseq)
  `uvm_object_new

  int num_transactions = 2;

  virtual task start_spi_host_trans(int num_transactions);
    cfg.seq_cfg.std_en  = 1;
    cfg.seq_cfg.dual_en = 1;
    //TODO: enable quad_en
    cfg.seq_cfg.quad_en = 0;
    super.start_spi_host_trans(num_transactions);
  endtask

endclass : spi_host_speed_vseq

