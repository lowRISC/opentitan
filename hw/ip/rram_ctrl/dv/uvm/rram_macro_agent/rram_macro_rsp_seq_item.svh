// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for responses sent by rram_macro. Nothing is randomised because the agent using it
// is passive only.

class rram_macro_rsp_seq_item extends uvm_sequence_item;
  `uvm_object_utils(rram_macro_rsp_seq_item)

  bit                 m_err;
  bit [2:0]           m_ecc_err;
  bit [DataWidth-1:0] m_rd_data;
  bit                 m_init_done;
  bit                 m_fatal_err;
  bit                 m_recov_err;

  // The request sequence item to which this is responding
  rram_macro_req_seq_item   m_req;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);
endclass

function rram_macro_rsp_seq_item::new(string name="");
  super.new(name);
endfunction

function void rram_macro_rsp_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_err", m_err, 1);
  printer.print_field_int("m_ecc_err", m_ecc_err, 3, UVM_BIN);
  printer.print_field("m_rd_data", m_rd_data, DataWidth, UVM_HEX);
  printer.print_field_int("m_init_done", m_init_done, 1);
  printer.print_field_int("m_fatal_err", m_fatal_err, 1);
  printer.print_field_int("m_recov_err", m_recov_err, 1);

  printer.print_object("m_req", m_req);
endfunction
