// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for key responses from otp_ctrl that will be driven by the agent

class nvm_otp_key_rsp_drive_seq_item extends nvm_otp_key_rsp_seq_item;
  `uvm_object_utils(nvm_otp_key_rsp_drive_seq_item)

  // The number of cycles of delay to wait before asserting ack.
  rand int unsigned m_delay_cycles;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);

  // A constraint on the maximum bound to the delay (to stop simulations taking ages).
  //
  // This is soft, which will allow a sequence to request a longer response time.
  extern constraint delay_bound_c;
endclass

function nvm_otp_key_rsp_drive_seq_item::new(string name="");
  super.new(name);
endfunction

function void nvm_otp_key_rsp_drive_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_delay_cycles", m_delay_cycles, 32, UVM_NORADIX);
endfunction

constraint nvm_otp_key_rsp_drive_seq_item::delay_bound_c {
  soft m_delay_cycles <= 10;
}
