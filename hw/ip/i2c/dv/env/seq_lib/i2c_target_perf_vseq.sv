// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// targetmode performance test vseq
class i2c_target_perf_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_perf_vseq)
  `uvm_object_new

  // Fast timing values programmed to registers
  // See constraint minimum in i2c_target_smoke_vseq
  constraint timing_val_c {
    t_r       == 1;
    t_f       == 1;
    thd_sta   == 3;
    tsu_sto   == 1;
    tsu_dat   == 1;
    thd_dat   == 1;
    t_timeout == 1;
    e_timeout == 1;
    tsu_sta   == 1;

    thigh     == 3;
    tlow      == 8;
    // tHoldStop must be at least 2 cycles which implies, t_r + t_buf - tsu_sta >= 2
    // in order for stop condition to propogate to internal FSM via prim flop
    t_buf     >= tsu_sta - t_r + 2;
    // In addition, t_buf > thd_dat + 1 to satisfy the Start/Stop decoder,
    // which rejects decoding Start/Stop symbols if SCL changes after SDA within
    // thd_dat cycles (+1 for CDC skew)
    t_buf     == thd_dat + 2;
  }

endclass
