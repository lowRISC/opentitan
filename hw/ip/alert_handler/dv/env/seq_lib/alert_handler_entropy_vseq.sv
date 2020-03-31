// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence triggers escalation by the interrupt timeout

class alert_handler_entropy_vseq extends alert_handler_sanity_vseq;
  `uvm_object_utils(alert_handler_entropy_vseq)

  `uvm_object_new

  rand bit drive_entropy;
  rand bit lock_regen;

  // TODO: re-evaluate the constraint based on ping coverage data
  constraint num_trans_c {
    num_trans inside {[4000:8000]};
  }

  virtual task alert_handler_init(bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en = '1,
                                  bit [alert_pkg::NAlerts-1:0]        alert_en = '1,
                                  bit [TL_DW-1:0]                     alert_class = 'h0,
                                  bit [NUM_LOCAL_ALERT-1:0]           loc_alert_en = '1,
                                  bit [TL_DW-1:0]                     loc_alert_class = 'h0);
    super.alert_handler_init(intr_en, alert_en, alert_class, loc_alert_en, loc_alert_class);
    cfg.entropy_vif.drive(drive_entropy);
    csr_wr(.csr(ral.regen), .value(lock_regen));
  endtask

endclass : alert_handler_entropy_vseq
