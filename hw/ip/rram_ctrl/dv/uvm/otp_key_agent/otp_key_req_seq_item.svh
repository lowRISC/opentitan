// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for key requests to otp_ctrl

class otp_key_req_seq_item extends uvm_sequence_item;
  `uvm_object_utils(otp_key_req_seq_item)

  // True if this is a data request (rather than an address request)
  rand bit m_is_data_req;

  extern function new (string name="");
  extern virtual function void do_print(uvm_printer printer);
endclass

function otp_key_req_seq_item::new (string name="");
  super.new(name);
endfunction

function void otp_key_req_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_is_data_req", m_is_data_req, 1);
endfunction
