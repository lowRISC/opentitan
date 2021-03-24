// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence enable signal intergrity fail.

class alert_handler_sig_int_fail_vseq extends alert_handler_smoke_vseq;
  `uvm_object_utils(alert_handler_sig_int_fail_vseq)

  `uvm_object_new

  constraint sig_int_c {
    esc_int_err == 0;
  }

  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {accum_thresh[i] dist {[0:1] :/ 5, [2:10] :/ 5};}
  }

  function void pre_randomize();
    this.enable_one_alert_c.constraint_mode(0);
    this.enable_classa_only_c.constraint_mode(0);
  endfunction

endclass : alert_handler_sig_int_fail_vseq
