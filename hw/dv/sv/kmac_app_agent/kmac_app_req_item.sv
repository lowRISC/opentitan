// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This item represents information sent from an application to KMAC (to make a request)
//
// When the agent is in Host mode, these sequence items will be randomised and then will be sent by
// kmac_app_host_driver. In Device mode, these sequence items are created as part of packets (that
// expect responses) by kmac_app_device_driver. In all modes, they will be created by the monitor
// (also as part of packets).

class kmac_app_req_item extends uvm_sequence_item;
  `uvm_object_utils(kmac_app_req_item)

  // Bytes of data in two shares
  rand bit [MsgWidth-1:0] m_data_s0;
  rand bit [MsgWidth-1:0] m_data_s1;

  // The number of valid bytes (encoded on the bus with the strb signal)
  rand int unsigned       m_num_bytes;

  // A flag that shows this is the last item in the packet
  rand bit                m_last;

  // Number of cycles of delay to wait before presenting the request. If the item has been captured
  // from the bus, this value will be zero.
  rand int unsigned       m_delay;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Add the bytes of the given share to the end of byte_queue
  extern function void add_share_to_byte_queue(bit share_idx, ref byte unsigned byte_queue[$]);

  // Constrain the possible values of m_num_bytes. It must be at most MsgWidth/8.
  //
  // Note that this is allowed to be less than MsgWidth/8 (and can even be zero). When using a
  // masked interface, the higher-level protocol expects a partial message to have m_last=1 or to be
  // followed by a message with m_num_bytes=0 and m_last=1.
  //
  // When generating a sequence of kmac_app_req_item items, kmac_app_host_seq ensures that this
  // constraint holds.
  extern constraint byte_length_c;

  // Constrain m_delay to be reasonable (to avoid a delay of 2^32 cycles).
  extern constraint max_delay_c;
endclass

function kmac_app_req_item::new(string name="");
  super.new(name);
endfunction

function void kmac_app_req_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field("m_data_s0", m_data_s0, MsgWidth, UVM_HEX);
  printer.print_field("m_data_s1", m_data_s1, MsgWidth, UVM_HEX);
  printer.print_field_int("m_num_bytes", m_num_bytes, 32, UVM_DEC);
  printer.print_field_int("m_last", m_last, 1, UVM_BIN);
  printer.print_field_int("m_delay", m_delay, 32, UVM_DEC);
endfunction

function void kmac_app_req_item::do_copy(uvm_object rhs);
  kmac_app_req_item rhs_;
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_data_s0 = rhs_.m_data_s0;
  this.m_data_s1 = rhs_.m_data_s1;
  this.m_num_bytes = rhs_.m_num_bytes;
  this.m_last = rhs_.m_last;
  this.m_delay = rhs_.m_delay;
endfunction

function bit kmac_app_req_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  kmac_app_req_item rhs_;

  // These items are only equivalent if rhs is actually a kmac_app_req_item.
  if (rhs == null || !$cast(rhs_, rhs)) return 0;

  // Check all the fields that are visible in an object monitored from the bus. This doesn't include
  // m_delay, because that is configuration for a driver.
  return (super.do_compare(rhs, comparer) &
          comparer.compare_field("m_data_s0", m_data_s0, rhs_.m_data_s0, MsgWidth) &
          comparer.compare_field("m_data_s1", m_data_s1, rhs_.m_data_s1, MsgWidth) &
          comparer.compare_field_int("m_num_bytes", m_num_bytes, rhs_.m_num_bytes, 32) &
          comparer.compare_field_int("m_last", m_last, rhs_.m_last, 1));
endfunction

function void kmac_app_req_item::add_share_to_byte_queue(bit               share_idx,
                                                         ref byte unsigned byte_queue[$]);
  for (int unsigned i = 0; i < m_num_bytes; i++) begin
    byte_queue.push_back(((share_idx ? m_data_s1 : m_data_s0) >> (8 * i)) & 8'hff);
  end
endfunction

constraint kmac_app_req_item::byte_length_c {
  m_num_bytes <= MsgWidth / 8;
}

constraint kmac_app_req_item::max_delay_c {
  soft m_delay <= 100;
}
