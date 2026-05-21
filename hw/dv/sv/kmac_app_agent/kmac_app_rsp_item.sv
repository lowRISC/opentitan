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
  rand bit [AppDigestW-1:0] m_digest_s0;
  rand bit [AppDigestW-1:0] m_digest_s1;
  rand bit                  m_error;
  rand bit                  m_finish;

  // The number of cycles taken between the request and the cycle where the response was presented
  rand int unsigned m_delay;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  extern function bit is_kmac_rsp_data_invalid();
  extern static function bit is_constant_share(bit [AppDigestW-1:0] share);

  // Constrain m_delay to be reasonable (to avoid a delay of 2^32 cycles).
  extern constraint max_delay_c;
endclass

function kmac_app_rsp_item::new(string name="");
  super.new(name);
endfunction

function void kmac_app_rsp_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_digest_s0", m_digest_s0, AppDigestW, UVM_HEX);
  printer.print_field_int("m_digest_s1", m_digest_s1, AppDigestW, UVM_HEX);
  printer.print_field_int("m_error",  m_error, 1, UVM_BIN);
  printer.print_field_int("m_finish", m_finish, 1, UVM_BIN);
  printer.print_field_int("m_delay",  m_delay, 32, UVM_DEC);
endfunction

function void kmac_app_rsp_item::do_copy(uvm_object rhs);
  kmac_app_rsp_item rhs_;
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_digest_s0 = rhs_.m_digest_s0;
  this.m_digest_s1 = rhs_.m_digest_s1;
  this.m_error = rhs_.m_error;
  this.m_finish = rhs_.m_finish;
  this.m_delay = rhs_.m_delay;
endfunction

function bit kmac_app_rsp_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  kmac_app_rsp_item rhs_;

  // These items are only equivalent if rhs is actually a kmac_app_rsp_item.
  if (rhs == null || !$cast(rhs_, rhs)) return 0;

  // Check all the fields that are visible in an object monitored from the bus. This doesn't include
  // m_delay, because that is configuration for a driver.
  return (super.do_compare(rhs, comparer) &
          comparer.compare_field("m_digest_s0", m_digest_s0, rhs_.m_digest_s0, AppDigestW) &
          comparer.compare_field("m_digest_s1", m_digest_s1, rhs_.m_digest_s1, AppDigestW) &
          comparer.compare_field_int("m_error", m_error, rhs_.m_error, 1) &
          comparer.compare_field_int("m_finish", m_finish, rhs_.m_finish, 1));
endfunction

function bit kmac_app_rsp_item::is_kmac_rsp_data_invalid();
  return is_constant_share(m_digest_s0) || is_constant_share(m_digest_s1);
endfunction

function bit kmac_app_rsp_item::is_constant_share(bit [AppDigestW-1:0] share);
  return share inside {'0, '1};
endfunction

constraint kmac_app_rsp_item::max_delay_c {
  soft m_delay <= 100;
}
