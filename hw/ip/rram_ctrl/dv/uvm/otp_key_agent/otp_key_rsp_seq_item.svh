// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for key responses from otp_ctrl

class otp_key_rsp_seq_item extends uvm_sequence_item;
  `uvm_object_utils(otp_key_rsp_seq_item)

  rand bit [NvmKeyWidth-1:0] m_key;
  rand bit [NvmKeyWidth-1:0] m_rand_key;
  rand bit                   m_seed_valid;

  // The number of cycles of delay to wait before asserting ack.
  rand int unsigned          m_delay_cycles;

  // The request sequence item to which this is responding
  otp_key_req_seq_item       m_req;

  extern function new (string name="");
  extern virtual function void do_print(uvm_printer printer);

  // A constraint on the maximum bound to the delay (to stop simulations taking ages). This is soft,
  // which will allow a sequence to request a longer response time.
  extern constraint delay_bound_c;
endclass

function otp_key_rsp_seq_item::new (string name="");
  super.new(name);
endfunction

function void otp_key_rsp_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field("m_key", m_key, NvmKeyWidth, UVM_HEX);
  printer.print_field("m_rand_key", m_rand_key, NvmKeyWidth, UVM_HEX);
  printer.print_field_int("m_seed_valid", m_seed_valid, 1, UVM_NORADIX);
  printer.print_field_int("m_delay_cycles", m_delay_cycles, 32, UVM_NORADIX);
  printer.print_object("m_req", m_req);
endfunction

constraint otp_key_rsp_seq_item::delay_bound_c {
  soft m_delay_cycles <= 10;
}
