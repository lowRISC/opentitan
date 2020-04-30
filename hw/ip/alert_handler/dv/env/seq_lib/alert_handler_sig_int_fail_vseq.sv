// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence enable signal intergrity fail.

class alert_handler_sig_int_fail_vseq extends alert_handler_sanity_vseq;
  `uvm_object_utils(alert_handler_sig_int_fail_vseq)

  `uvm_object_new

  function void pre_randomize();
    this.enable_one_alert_c.constraint_mode(0);
    this.enable_classa_only_c.constraint_mode(0);
    this.sig_int_c.constraint_mode(0);
  endfunction

  virtual task alert_handler_init(bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en = '1,
                                  bit [alert_pkg::NAlerts-1:0]        alert_en = '1,
                                  bit [TL_DW-1:0]                     alert_class = 'h0,
                                  bit [NUM_LOCAL_ALERT-1:0]           loc_alert_en = '1,
                                  bit [TL_DW-1:0]                     loc_alert_class = 'h0);
    super.alert_handler_init(intr_en, alert_en, alert_class, loc_alert_en, loc_alert_class);
   // lock regen to avoid changing real config settings during escalation
    csr_wr(.csr(ral.regen), .value(1));
  endtask
endclass : alert_handler_sig_int_fail_vseq
