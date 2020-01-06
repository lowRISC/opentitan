// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Alert sender receiver sequence item
// ---------------------------------------------

class alert_seq_item extends uvm_sequence_item;

  rand bit alert_send;
  rand bit alert_rsp; // receiver response to alert using ack
  rand bit alert_int_err;
  rand bit ping_rsp; // sender response to ping using alert
  rand bit ack_int_err;
  rand bit ping_send;
  rand bit ping_int_err;
  rand bit timeout;

  // for alert_monitor
  rand alert_type_e      alert_type;
  rand alert_handshake_e alert_handshake_sta;

  // delays
  rand int unsigned ping_delay;
  rand int unsigned ack_delay;
  rand int unsigned ack_stable;
  rand int unsigned alert_delay;

  constraint delay_c {
    soft ping_delay  dist {0 :/ 5, [1:10] :/ 5};
    soft ack_delay   dist {0 :/ 5, [1:10] :/ 5};
    soft alert_delay dist {0 :/ 5, [1:10] :/ 5};
    soft ack_stable  dist {1 :/ 5, [2:10] :/ 5};
  }

  `uvm_object_utils_begin(alert_seq_item)
    `uvm_field_int (alert_send,    UVM_DEFAULT)
    `uvm_field_int (alert_int_err, UVM_DEFAULT)
    `uvm_field_int (alert_rsp,     UVM_DEFAULT)
    `uvm_field_int (ping_rsp,      UVM_DEFAULT)
    `uvm_field_int (ack_int_err,   UVM_DEFAULT)
    `uvm_field_int (ping_send,     UVM_DEFAULT)
    `uvm_field_int (ping_int_err,  UVM_DEFAULT)
    `uvm_field_int (timeout,       UVM_DEFAULT)
    `uvm_field_enum(alert_type_e, alert_type, UVM_DEFAULT)
    `uvm_field_enum(alert_handshake_e, alert_handshake_sta, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
  endfunction : new

endclass : alert_seq_item
