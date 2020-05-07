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

  constraint lock_bit_c {
    do_lock_config == 1;
  }

  function void pre_randomize();
    this.enable_classa_only_c.constraint_mode(0);
    // set verbosity high to avoid printing out too much information
    verbosity = UVM_HIGH;
  endfunction

endclass : alert_handler_entropy_vseq
