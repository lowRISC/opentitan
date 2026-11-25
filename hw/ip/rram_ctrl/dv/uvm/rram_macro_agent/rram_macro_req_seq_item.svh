// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for requests sent to rram_macro. Nothing is randomised because the agent using it
// is passive only.

class rram_macro_req_seq_item extends uvm_sequence_item;
  `uvm_object_utils(rram_macro_req_seq_item)

  bit                 m_rd_req;
  bit                 m_wr_req;
  bit                 m_wr_last;
  bit [AddrW-1:0]     m_addr;
  bit [DataWidth-1:0] m_wr_data;
  rram_part_e         m_part;
  bit                 m_ecc_en;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);
endclass

function rram_macro_req_seq_item::new(string name="");
  super.new(name);
endfunction

function void rram_macro_req_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_rd_req", m_rd_req, 1);
  printer.print_field_int("m_wr_req", m_wr_req, 1);
  printer.print_field_int("m_wr_last", m_wr_last, 1);
  printer.print_field_int("m_addr", m_addr, AddrW, UVM_HEX);
  printer.print_field("m_wr_data", m_wr_data, DataWidth, UVM_HEX);
  printer.print_generic("m_part", "rram_part_e", 1, $sformatf("%0s (%0d)", m_part.name(), m_part));
  printer.print_field_int("m_ecc_en", m_ecc_en, 1);
endfunction
