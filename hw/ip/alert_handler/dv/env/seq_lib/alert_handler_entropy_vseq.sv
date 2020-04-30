// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence enable entropy by writing 1 to the lock_regen register.

class alert_handler_entropy_vseq extends alert_handler_sanity_vseq;
  `uvm_object_utils(alert_handler_entropy_vseq)

  `uvm_object_new

  rand bit drive_entropy;
  rand bit lock_regen;

  // large number of num_trans to make sure covers all alerts and escalation pings
  constraint num_trans_c {
    num_trans inside {[4000:100_000]};
  }

  // increase the possibility to enable more alerts, because alert_handler only sends ping on
  // enabled alerts
  constraint enable_one_alert_c {
    alert_en dist {'b1111 := 9, [0:'b1110] := 1};
  }

  // temp constraint, should take off when support ping_int_err
  constraint sig_int_c {
    esc_int_err == 0;
  }

  function void pre_randomize();
    this.enable_classa_only_c.constraint_mode(0);
    // set verbosity high to avoid printing out too much information
    verbosity = UVM_HIGH;
  endfunction

  virtual task alert_handler_init(bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en = '1,
                                  bit [alert_pkg::NAlerts-1:0]        alert_en = '1,
                                  bit [TL_DW-1:0]                     alert_class = 'h0,
                                  bit [NUM_LOCAL_ALERT-1:0]           loc_alert_en = '1,
                                  bit [TL_DW-1:0]                     loc_alert_class = 'h0);
    super.alert_handler_init(intr_en, alert_en, alert_class, loc_alert_en, loc_alert_class);
    cfg.entropy_vif.drive(drive_entropy);
    if (ral.regen.get_mirrored_value() == 1) begin
      `uvm_info(`gfn,
          $sformatf("init setting: intr_en=%0b, alert_en=%0b, alert_class=%0b, regen=%0b",
          intr_en, alert_en, alert_class, lock_regen), UVM_LOW)
    end
    csr_wr(.csr(ral.regen), .value(lock_regen));
  endtask

endclass : alert_handler_entropy_vseq
