// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence responses to alert pins by sending the ack pins
class alert_receiver_alert_rsp_seq extends alert_receiver_base_seq;

  `uvm_object_utils(alert_receiver_alert_rsp_seq)
  `uvm_object_new

  constraint alert_receiver_alert_rsp_seq_c {
    r_alert_ping_send == 0;
    r_alert_rsp       == 1;
  }

endclass : alert_receiver_alert_rsp_seq
