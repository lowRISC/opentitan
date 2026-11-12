// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A reactive sequence that responds to requests, responding with a key each time.

class otp_key_seq extends uvm_sequence #(.REQ (otp_key_rsp_seq_item));
  `uvm_object_utils(otp_key_seq)
  `uvm_declare_p_sequencer(otp_key_sequencer)

  extern function new (string name="");
  extern virtual task body();

  extern local task send_response(otp_key_req_seq_item key_req);
endclass

function otp_key_seq::new(string name="");
  super.new(name);
endfunction

task otp_key_seq::body();
  forever begin
    otp_key_req_seq_item key_req;
    p_sequencer.m_req_fifo.get(key_req);
    send_response(key_req);
  end
endtask

task otp_key_seq::send_response(otp_key_req_seq_item key_req);
  otp_key_rsp_seq_item item = otp_key_rsp_seq_item::type_id::create("item");

  item.m_req = key_req;

  start_item(item);

  if (!item.randomize()) begin
    `uvm_fatal("rand_failed", "Failed to randomize response item.")
  end

  finish_item(item);
endtask
