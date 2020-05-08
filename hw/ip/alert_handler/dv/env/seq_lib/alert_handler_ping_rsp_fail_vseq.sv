// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence add ping timeout error based on the entropy test.

class alert_handler_ping_rsp_fail_vseq extends alert_handler_entropy_vseq;
  `uvm_object_utils(alert_handler_ping_rsp_fail_vseq)

  `uvm_object_new

  constraint sig_int_c {
    esc_int_err == '1;
    esc_standalone_int_err dist {0 := 9, [1:'b1111] := 1};
  }

endclass : alert_handler_ping_rsp_fail_vseq
