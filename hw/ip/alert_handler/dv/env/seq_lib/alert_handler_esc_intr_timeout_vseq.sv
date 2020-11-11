// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence triggers escalation by the interrupt timeout

class alert_handler_esc_intr_timeout_vseq extends alert_handler_smoke_vseq;
  `uvm_object_utils(alert_handler_esc_intr_timeout_vseq)

  `uvm_object_new

  constraint esc_due_to_intr_timeout_only_c {
    foreach (accum_thresh[i]) {accum_thresh[i] > 1;} // prevent alert accumulation triggers esc
    do_esc_intr_timeout == 1;
  }

endclass : alert_handler_esc_intr_timeout_vseq
