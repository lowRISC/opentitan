// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// targetmode performance test vseq
class i2c_target_perf_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_perf_vseq)

  class target_perf_timing_cfg extends i2c_timing_cfg;
    // Fast timing values programmed to registers
    constraint target_perf_c {
      tc.t_r      == 1;
      tc.t_f      == 1;
      tc.thd_sta  == 3;
      tc.tsu_sto  == 1;
      tc.tsu_dat  == 1;
      tc.thd_dat  == 1;
      tc.tTimeout == 1;
      tc.eTimeout == 1;
      tc.tsu_sta  == 1;

      tc.thigh    == 4;
      tc.tlow     == 8;
    }
  endclass : target_perf_timing_cfg

  function new (string name="");
    target_perf_timing_cfg tptc = new;
    super.new(name);
    `downcast(tcc, tptc);
    // Disable the baseclass constraints, as it would conflict.
    tcc.timing_val_minmax_c.constraint_mode(0);
    tcc.tsu_sta_minmax_c.constraint_mode(0);
    tcc.implementation_c.constraint_mode(0);
    tcc.agent_c.constraint_mode(0);
    tcc.error_stimulus_c.constraint_mode(0); // No errors
    tcc.t_timeout_c.constraint_mode(0);
  endfunction : new

endclass
