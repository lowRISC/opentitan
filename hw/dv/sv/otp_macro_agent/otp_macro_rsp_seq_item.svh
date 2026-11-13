// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for the response to an OTP macro request

class otp_macro_rsp_seq_item extends uvm_sequence_item;
  `uvm_object_utils(otp_macro_rsp_seq_item)

  // The data returned by the responder. Word k of the transfer is in bits [k*OtpWidth +: OtpWidth].
  otp_macro_data_t       m_rdata;

  // The error code returned by the responder
  err_e                  m_err;

  // The request to which this is the response
  otp_macro_req_seq_item m_req;

  extern function new (string name="");
  extern virtual function void do_print(uvm_printer printer);

  // Returns word `idx` of m_rdata.
  extern function bit [OtpWidth-1:0] get_rdata_word(int unsigned idx);
endclass

function otp_macro_rsp_seq_item::new (string name="");
  super.new(name);
endfunction

function void otp_macro_rsp_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  if (m_req != null && m_req.m_cmd inside {Read, ReadRaw, Zeroize}) begin
    printer.print_array_header("m_rdata", m_req.m_size + 1);
    for (int unsigned k = 0; k <= m_req.m_size; k++) begin
      printer.print_field_int($sformatf("[%0d]", k), get_rdata_word(k), OtpWidth, UVM_HEX);
    end
    printer.print_array_footer(m_req.m_size + 1);
  end
  printer.print_string("m_err", $sformatf("%0s (%0d)", m_err.name(), m_err));
  printer.print_object("m_req", m_req);
endfunction

function bit [OtpWidth-1:0] otp_macro_rsp_seq_item::get_rdata_word(int unsigned idx);
  return m_rdata[idx * OtpWidth +: OtpWidth];
endfunction
