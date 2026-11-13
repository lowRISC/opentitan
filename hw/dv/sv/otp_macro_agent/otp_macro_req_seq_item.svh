// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for a request that otp_ctrl sends on the OTP macro interface

class otp_macro_req_seq_item extends uvm_sequence_item;
  `uvm_object_utils(otp_macro_req_seq_item)

  // The command to run
  rand cmd_e            m_cmd;

  // The number of OTP words to transfer, minus one
  rand otp_macro_size_t m_size;

  // The address of the first OTP word to transfer
  rand otp_macro_addr_t m_addr;

  // The data for a write. Word k of the transfer is in bits [k*OtpWidth +: OtpWidth].
  rand otp_macro_data_t m_wdata;

  // The number of cycles the driver waits before presenting the request
  rand int unsigned     m_delay_cycles;

  extern function new (string name="");
  extern virtual function void do_print(uvm_printer printer);

  // Returns word `idx` of m_wdata.
  extern function bit [OtpWidth-1:0] get_wdata_word(int unsigned idx);

  // Commands otp_ctrl sends after Init. Init itself is sent on purpose, not picked at random, so
  // this is soft.
  extern constraint cmd_c;

  // otp_ctrl only ever transfers 1, 2 or 4 words at a time.
  extern constraint size_c;

  // A transfer is aligned to its size and stays within the OTP.
  extern constraint addr_c;

  // A bound on the delay (to stop simulations taking ages). This is soft, which allows a sequence
  // to ask for a longer delay.
  extern constraint delay_bound_c;
endclass

function otp_macro_req_seq_item::new (string name="");
  super.new(name);
endfunction

function void otp_macro_req_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_string("m_cmd", m_cmd.name());
  printer.print_field_int("m_size", m_size, $bits(m_size), UVM_DEC);
  printer.print_field_int("m_addr", m_addr, $bits(m_addr), UVM_HEX);
  if (m_cmd inside {Write, WriteRaw}) begin
    printer.print_array_header("m_wdata", m_size + 1);
    for (int unsigned k = 0; k <= m_size; k++) begin
      printer.print_field_int($sformatf("[%0d]", k), get_wdata_word(k), OtpWidth, UVM_HEX);
    end
    printer.print_array_footer(m_size + 1);
  end
  printer.print_field_int("m_delay_cycles", m_delay_cycles, 32, UVM_DEC);
endfunction

function bit [OtpWidth-1:0] otp_macro_req_seq_item::get_wdata_word(int unsigned idx);
  return m_wdata[idx * OtpWidth +: OtpWidth];
endfunction

constraint otp_macro_req_seq_item::cmd_c {
  soft m_cmd inside {Read, Write, ReadRaw, WriteRaw, Zeroize};
}

constraint otp_macro_req_seq_item::size_c {
  m_size inside {0, 1, 3};
}

constraint otp_macro_req_seq_item::addr_c {
  (m_addr % (m_size + 1)) == 0;
  (m_addr + m_size) < OtpDepth;
}

constraint otp_macro_req_seq_item::delay_bound_c {
  soft m_delay_cycles <= 10;
}
