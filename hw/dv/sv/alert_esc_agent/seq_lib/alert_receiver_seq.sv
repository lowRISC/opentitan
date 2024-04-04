// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence send ping_p and ping_n to trigger ping signals
class alert_receiver_seq extends alert_receiver_base_seq;

  `uvm_object_utils(alert_receiver_seq)

  `uvm_object_new

  constraint alert_receiver_seq_c {
    r_alert_ping_send == 1;
    r_alert_rsp       == 0;
  }

endclass : alert_receiver_seq
