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

  // Bytes of data
  rand bit [MsgWidth-1:0] m_data;

  // The number of valid bytes (encoded on the bus with the strb signal)
  rand int unsigned       m_num_bytes;

  // A flag that shows this is the last item in the packet
  rand bit unsigned       m_last;

  // Number of cycles of delay to wait before presenting the request. If the item has been captured
  // from the bus, this value will be zero.
  rand int unsigned       m_delay;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);

  // Add the bytes in this request to the end of queue
  extern function void add_to_byte_queue(ref byte queue[$]);

  // Constrain the possible values of m_num_bytes (at most MsgWidth/8)
  extern constraint byte_length_c;
endclass

function kmac_app_req_item::new(string name="");
  super.new(name);
endfunction

function void kmac_app_req_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_data", m_data, MsgWidth, UVM_HEX);
  printer.print_field_int("m_num_bytes", m_num_bytes, 32, UVM_NORADIX);
  printer.print_field_int("m_last", m_last, 1, UVM_NORADIX);
  printer.print_field_int("m_delay", m_delay, 32, UVM_NORADIX);
endfunction

function void kmac_app_req_item::do_copy(uvm_object rhs);
  kmac_app_req_item rhs_;
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_data = rhs_.m_data;
  this.m_num_bytes = rhs_.m_num_bytes;
  this.m_last = rhs_.m_last;
  this.m_delay = rhs_.m_delay;
endfunction

function void kmac_app_req_item::add_to_byte_queue(ref byte queue[$]);
  for (int unsigned i = 0; i < m_num_bytes; i++) begin
    queue.push_back((m_data >> (8 * i)) & 8'hff);
  end
endfunction

constraint kmac_app_req_item::byte_length_c {
  m_num_bytes <= MsgWidth / 8;
}
