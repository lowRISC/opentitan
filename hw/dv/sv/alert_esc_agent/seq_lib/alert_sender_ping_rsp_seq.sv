// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to ping pins by sending the alert pins
class alert_sender_ping_rsp_seq extends alert_sender_base_seq;

  `uvm_object_utils(alert_sender_ping_rsp_seq)
  `uvm_object_new

  constraint alert_sender_ping_rsp_seq_c {
    s_alert_send     == 0;
    s_alert_ping_rsp == 1;
  }

endclass : alert_sender_ping_rsp_seq
