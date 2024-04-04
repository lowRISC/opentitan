// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence send the alert pins to the receiver
class alert_sender_seq extends alert_sender_base_seq;

  `uvm_object_utils(alert_sender_seq)
  `uvm_object_new

  constraint alert_sender_seq_c {
    s_alert_send     == 1;
    s_alert_ping_rsp == 0;
    ping_timeout     == 0;
  }

endclass : alert_sender_seq
