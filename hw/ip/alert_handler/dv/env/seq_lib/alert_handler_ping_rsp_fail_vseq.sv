// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence add ping timeout error based on the entropy test.

class alert_handler_ping_rsp_fail_vseq extends alert_handler_entropy_vseq;
  `uvm_object_utils(alert_handler_ping_rsp_fail_vseq)

  `uvm_object_new

  // always enable clr_en to hit the case when escalation ping interrupted by real esc sig
  constraint clr_and_lock_en_c {
    clr_en == '1;
    lock_bit_en == 0;
  }

  constraint sig_int_c {
    esc_int_err == '1;
    esc_standalone_int_err dist {
      0 :/ 9,
      [1 : 'b1111] :/ 1
    };
    alert_ping_timeout == '1;
  }

  constraint ping_timeout_cyc_c {ping_timeout_cyc inside {[0 : 100]};}
endclass : alert_handler_ping_rsp_fail_vseq
