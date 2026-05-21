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
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Find the requests where the given share is nonzero, adding their indices to req_indices and
  // returning the number found.
  extern function int unsigned get_reqs_with_nonzero_share(bit              share_idx,
                                                           ref int unsigned req_indices[$]);

  // Fill a queue with the bytes for the given share in the requests in this packet
  extern function void get_share_byte_queue(bit                  share_idx,
                                            output byte unsigned byte_queue[$]);
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

function bit kmac_app_req_packet_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  kmac_app_req_packet_item rhs_;
  bit all_match = 1;

  // These items are only equivalent if rhs is actually a kmac_app_req_packet_item.
  if (rhs == null || !$cast(rhs_, rhs)) return 0;

  if (!super.do_compare(rhs, comparer)) all_match = 0;

  // For two packets to match, they must have the same number of requests
  if (m_reqs.size() != rhs_.m_reqs.size()) begin
    comparer.print_msg($sformatf("Packet size mismatch (%0d != %0d)",
                                 m_reqs.size(), rhs_.m_reqs.size()));
    return 0;
  end

  // Given that they are of the same length, we can now check that each pair of requests matches.
  // If either request is null, something has gone wrong, and we treat it as a failure.
  foreach(m_reqs[i]) begin
    if (m_reqs[i] == null) begin
      all_match = 0;
      comparer.print_msg($sformatf("m_reqs[%0d] on LHS is null", i));
    end
    if (rhs_.m_reqs[i] == null) begin
      all_match = 0;
      comparer.print_msg($sformatf("m_reqs[%0d] on RHS is null", i));
    end

    if (m_reqs[i] != null && rhs_.m_reqs[i] != null) begin
      if (!m_reqs[i].compare(rhs_.m_reqs[i], comparer)) all_match = 0;
    end
  end

  return all_match;
endfunction

function int unsigned
  kmac_app_req_packet_item::get_reqs_with_nonzero_share(bit              share_idx,
                                                        ref int unsigned req_indices[$]);
  int unsigned count = 0;
  foreach (m_reqs[i]) begin
    if (|(share_idx ? m_reqs[i].m_data_s1 : m_reqs[i].m_data_s0)) begin
      req_indices.push_back(i);
      count++;
    end
  end
  return count;
endfunction

function void kmac_app_req_packet_item::get_share_byte_queue(bit                  share_idx,
                                                             output byte unsigned byte_queue[$]);
  foreach (m_reqs[i]) m_reqs[i].add_share_to_byte_queue(share_idx, byte_queue);
endfunction
