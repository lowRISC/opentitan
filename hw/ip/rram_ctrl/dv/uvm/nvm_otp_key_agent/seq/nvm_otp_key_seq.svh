// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A reactive sequence that responds to requests, responding with a key each time.

class nvm_otp_key_seq extends uvm_sequence #(.REQ (nvm_otp_key_rsp_seq_item));
  `uvm_object_utils(nvm_otp_key_seq)
  `uvm_declare_p_sequencer(nvm_otp_key_sequencer)

  extern function new (string name="");
  extern virtual task body();

  extern local task send_response(nvm_otp_key_req_seq_item key_req);
endclass

function nvm_otp_key_seq::new(string name="");
  super.new(name);
endfunction

task nvm_otp_key_seq::body();
  forever begin
    nvm_otp_key_req_seq_item key_req;
    p_sequencer.m_req_fifo.get(key_req);
    send_response(key_req);
  end
endtask

task nvm_otp_key_seq::send_response(nvm_otp_key_req_seq_item key_req);
  nvm_otp_key_rsp_seq_item item = nvm_otp_key_rsp_seq_item::type_id::create("item");

  item.m_req = key_req;

  start_item(item);

  if (!item.randomize()) begin
    `uvm_fatal("rand_failed", "Failed to randomize response item.")
  end

  finish_item(item);
endtask
