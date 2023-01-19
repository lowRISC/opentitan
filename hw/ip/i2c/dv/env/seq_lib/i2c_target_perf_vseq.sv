// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// targetmode performance test vseq
class i2c_target_perf_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_perf_vseq)
  `uvm_object_new

  // Fast timing values programmed to registers
  // See constraint minimum in i2c_target_smoke_vseq
  constraint timing_val_c {
    t_r       == 10;
    t_f       == 10;
    thd_sta   == 10;
    tsu_sto   == 10;
    tsu_dat   == 10;
    thd_dat   == 10;
    t_timeout == 10;
    e_timeout == 1;
    tsu_sta   == 10;

    thigh     == 10;
    tlow      == (7 + cfg.target_sync_delay);
    t_buf     == 10;
  }

endclass
