// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents an edge on the reset line (seen by a monitor)

class reset_edge_item extends uvm_sequence_item;
  `uvm_object_utils(reset_edge_item)

  // The state of the reset line after the edge.
  bit m_new_state;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass

function reset_edge_item::new(string name="");
  super.new(name);
endfunction

function void reset_edge_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_new_state", m_new_state, 1, UVM_BIN);
endfunction

function void reset_edge_item::do_copy(uvm_object rhs);
  reset_edge_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  this.m_new_state = rhs_.m_new_state;
endfunction

function bit reset_edge_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  reset_edge_item rhs_;

  // These items are only equivalent if rhs is actually a reset_edge_item.
  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not a reset_edge_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_new_state", m_new_state, rhs_.m_new_state, 1, UVM_BIN));
endfunction
