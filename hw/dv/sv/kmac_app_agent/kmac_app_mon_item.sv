// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An item created by the monitor that shows a request packet, together with a response

class kmac_app_mon_item extends uvm_sequence_item;
  `uvm_object_utils(kmac_app_mon_item)

  kmac_app_req_packet_item m_req;
  kmac_app_rsp_item        m_rsp;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
endclass

function kmac_app_mon_item::new(string name="");
  super.new(name);
  m_req = kmac_app_req_packet_item::type_id::create("m_req");
  m_rsp = kmac_app_rsp_item::type_id::create("m_rsp");
endfunction

function void kmac_app_mon_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_object("m_req", m_req);
  printer.print_object("m_rsp", m_rsp);
endfunction

function void kmac_app_mon_item::do_copy(uvm_object rhs);
  kmac_app_mon_item rhs_;
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")
  super.do_copy(rhs);
  if (!$cast(this.m_req, rhs_.m_req.clone())) `uvm_fatal("do_copy", "Casting m_req clone failed.")
  if (!$cast(this.m_rsp, rhs_.m_rsp.clone())) `uvm_fatal("do_copy", "Casting m_rsp clone failed.")
endfunction
