// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends one OTP macro command and collects its response.
//
// The command is m_req. Randomizing the sequence randomizes it, so a caller can pick a command
// with inline constraints, e.g. seq.randomize() with {m_req.m_cmd == Read;}, or set the fields of
// m_req directly. Once the sequence has finished, m_rsp holds the response, or is null if a reset
// interrupted the command.
//
// The driver finishes the item when the request is accepted, so several of these sequences can run
// at once (from different threads) and have their requests waiting for responses together.

class otp_macro_cmd_seq extends dv_base_seq #(.REQ         (otp_macro_req_seq_item),
                                              .RSP         (otp_macro_rsp_seq_item),
                                              .CFG_T       (otp_macro_agent_cfg),
                                              .SEQUENCER_T (otp_macro_sequencer));
  `uvm_object_utils(otp_macro_cmd_seq)

  // The command to send
  rand otp_macro_req_seq_item m_req;

  // The response to m_req, or null if a reset interrupted the command
  otp_macro_rsp_seq_item      m_rsp;

  extern function new (string name="");
  extern virtual task body();

  // Called by the sequencer when the driver returns a response
  extern virtual function void response_handler(uvm_sequence_item response);

  // The response, once the driver has returned it
  local otp_macro_rsp_seq_item m_received;
endclass

function otp_macro_cmd_seq::new(string name="");
  super.new(name);
  m_req = otp_macro_req_seq_item::type_id::create("m_req");
  use_response_handler(1);
endfunction

task otp_macro_cmd_seq::body();
  m_received = null;
  start_item(m_req);
  finish_item(m_req);

  // The request has been accepted, or dropped because of a reset. Wait for its response, which
  // will never come if there is a reset.
  wait (m_received != null || cfg.in_reset);
  m_rsp = m_received;
endtask

function void otp_macro_cmd_seq::response_handler(uvm_sequence_item response);
  if (!$cast(m_received, response)) begin
    `uvm_fatal("bad_rsp_type", "The driver returned a response of the wrong type.")
  end
endfunction
