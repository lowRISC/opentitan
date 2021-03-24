// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence triggers escalation by accumulating alerts in the same class.
// difference from smoke test, this sequence set the threshold to larger numbers.

class alert_handler_esc_alert_accum_vseq extends alert_handler_smoke_vseq;
  `uvm_object_utils(alert_handler_esc_alert_accum_vseq)

  `uvm_object_new

  constraint disable_clr_esc_c {
    do_clr_esc == 0;
  }

  constraint enable_alert_accum_esc_only_c {
    do_esc_intr_timeout == 0; // disable interrupt timeout triggered escalation
  }

  constraint num_trans_c {
    num_trans inside {[1:100]};
  }

  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {accum_thresh[i] inside {[0:100]};}
  }

endclass : alert_handler_esc_alert_accum_vseq
