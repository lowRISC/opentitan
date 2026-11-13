// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// One key handshake on nvm_otp_key_if.
//
// The item is used in three places:
// - The monitor sends a request item (only `kind` is set) to the sequencer as soon as it sees a
//   new request.
// - The device sequence turns that into a response item (key, rand_key, seed_valid and
//   ack_delay) for the driver.
// - The monitor sends a completed item (everything except ack_delay) on its analysis port once
//   the handshake has finished.
class nvm_otp_key_item extends uvm_sequence_item;

  // Which key is requested. Not randomized: it comes from the request line the DUT raised.
  nvm_otp_key_kind_e kind;

  rand nvm_otp_key_t key;
  rand nvm_otp_key_t rand_key;

  // Whether otp_ctrl reports the key seed as provisioned.
  rand bit seed_valid;

  // Driver only: number of extra clock cycles to wait before asserting the ack.
  rand int unsigned ack_delay;

  // Monitor only: number of clock cycles from the request being seen to the handshake.
  int unsigned req_to_ack_cycles;

  constraint seed_valid_c {
    soft seed_valid == 1'b1;
  }

  constraint ack_delay_c {
    soft ack_delay inside {[0:5]};
  }

  `uvm_object_utils_begin(nvm_otp_key_item)
    `uvm_field_enum(nvm_otp_key_kind_e, kind, UVM_DEFAULT)
    `uvm_field_int (key,                      UVM_DEFAULT)
    `uvm_field_int (rand_key,                 UVM_DEFAULT)
    `uvm_field_int (seed_valid,               UVM_DEFAULT)
    `uvm_field_int (ack_delay,                UVM_DEFAULT | UVM_DEC)
    `uvm_field_int (req_to_ack_cycles,        UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  extern function new(string name = "");
endclass : nvm_otp_key_item

function nvm_otp_key_item::new(string name = "");
  super.new(name);
endfunction : new
