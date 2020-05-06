// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence enable signal intergrity fail.

class alert_handler_sig_int_fail_vseq extends alert_handler_sanity_vseq;
  `uvm_object_utils(alert_handler_sig_int_fail_vseq)

  `uvm_object_new

  constraint lock_bit_c {
    do_lock_config == 1;
  }

  function void pre_randomize();
    this.enable_one_alert_c.constraint_mode(0);
    this.enable_classa_only_c.constraint_mode(0);
    this.sig_int_c.constraint_mode(0);
  endfunction

endclass : alert_handler_sig_int_fail_vseq
