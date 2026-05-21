// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This item represents information sent from KMAC back to the application.
//
// When the agent is in Device mode, these sequence items will be randomised and then will be sent
// by kmac_app_device_driver. In all modes, they will be created by the monitor.

class kmac_app_rsp_item extends uvm_sequence_item;
  `uvm_object_utils(kmac_app_rsp_item)

  // Response digest/error
  rand bit [AppDigestW-1:0] m_digest_share0;
  rand bit [AppDigestW-1:0] m_digest_share1;
  rand bit                  m_error;

  // The number of cycles taken between the request and the cycle where the response was presented
  rand int unsigned m_delay;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);

  extern function bit is_kmac_rsp_data_invalid();
  extern static function bit is_constant_share(bit [AppDigestW-1:0] share);
endclass

function kmac_app_rsp_item::new(string name="");
  super.new(name);
endfunction

function void kmac_app_rsp_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_digest_share0", m_digest_share0, AppDigestW, UVM_HEX);
  printer.print_field_int("m_digest_share1", m_digest_share1, AppDigestW, UVM_HEX);
  printer.print_field_int("m_error", m_error, 1, UVM_NORADIX);
  printer.print_field_int("m_delay", m_delay, 32, UVM_NORADIX);
endfunction

function void kmac_app_rsp_item::do_copy(uvm_object rhs);
  kmac_app_rsp_item rhs_;
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_digest_share0 = rhs_.m_digest_share0;
  this.m_digest_share1 = rhs_.m_digest_share1;
  this.m_error = rhs_.m_error;
  this.m_delay = rhs_.m_delay;
endfunction

function bit kmac_app_rsp_item::is_kmac_rsp_data_invalid();
  return is_constant_share(m_digest_share0) || is_constant_share(m_digest_share1);
endfunction

function bit kmac_app_rsp_item::is_constant_share(bit [AppDigestW-1:0] share);
  return share inside {'0, '1};
endfunction
