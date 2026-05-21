// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This item represents a complete packet sent from an application to KMAC (to make a request)
//
// These sequence items are created by the driver in Device mode (based on requests that the agent
// sees being sent). They are then sent to a reactive sequence, which will produce responses.

class kmac_app_req_packet_item extends uvm_sequence_item;
  `uvm_object_utils(kmac_app_req_packet_item)

  kmac_app_req_item m_reqs[$];

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);

  // Fill a queue with the bytes in the requests in this packet
  extern function void fill_byte_queue(output byte queue[$]);
endclass

function kmac_app_req_packet_item::new(string name="");
  super.new(name);
endfunction

function void kmac_app_req_packet_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_array_header("m_reqs", m_reqs.size(), "queue of kmac_app_req_item");
  foreach(m_reqs[i]) begin
    printer.print_object($sformatf("[%0d]", i), m_reqs[i]);
  end
  printer.print_array_footer(m_reqs.size());
endfunction

function void kmac_app_req_packet_item::do_copy(uvm_object rhs);
  kmac_app_req_packet_item rhs_;
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")
  super.do_copy(rhs);

  // Take a deep copy of rhs_.m_reqs by deleting anything that's currently in this.m_reqs and then
  // calling clone on each of the items in rhs_.m_reqs.
  this.m_reqs.delete();
  foreach (rhs_.m_reqs[i]) begin
    kmac_app_req_item req;
    if (!$cast(req, rhs_.m_reqs[i].clone())) `uvm_fatal("do_copy", "Cannot cast clone.")
    this.m_reqs.push_back(req);
  end
endfunction

function void kmac_app_req_packet_item::fill_byte_queue(output byte queue[$]);
  foreach (m_reqs[i]) m_reqs[i].add_to_byte_queue(queue);
endfunction
