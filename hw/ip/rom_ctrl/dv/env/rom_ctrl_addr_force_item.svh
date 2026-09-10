// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that can be driven by a rom_ctrl_addr_force_driver to force the address signal in
// an FSM's rom_ctrl_counter.

class rom_ctrl_addr_force_item extends uvm_sequence_item;
  `uvm_object_utils(rom_ctrl_addr_force_item)

  // The value of the word address when the force should be applied
  rand int unsigned m_start_addr;

  // The desired value of the word address (what it should be forced to)
  rand int unsigned m_desired_addr;

  // A bit that says that forcing this address should be aborted and the driver should finish
  // driving it immediately. Set this by calling abort(). Check it with get_aborted().
  local bit         m_aborted;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Abort this item, causing any driver to finish driving it immediately.
  extern function void abort();

  // Return true if abort() has been called. Wait for that to happen with wait_until_aborted().
  extern function bit get_aborted();

  // Wait until abort() is called.
  extern task wait_until_aborted();
endclass

function rom_ctrl_addr_force_item::new(string name = "");
  super.new(name);
endfunction

function void rom_ctrl_addr_force_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_start_addr", m_start_addr, 32, UVM_HEX);
  printer.print_field_int("m_desired_addr", m_desired_addr, 32, UVM_HEX);
  printer.print_field_int("m_aborted", m_aborted, 1, UVM_BIN);
endfunction

function void rom_ctrl_addr_force_item::do_copy(uvm_object rhs);
  rom_ctrl_addr_force_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  m_start_addr = rhs_.m_start_addr;
  m_desired_addr = rhs_.m_desired_addr;
  m_aborted = rhs_.m_aborted;
endfunction

function bit rom_ctrl_addr_force_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  rom_ctrl_addr_force_item rhs_;

  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not a rom_ctrl_addr_force_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field_int("m_start_addr",
                                     m_start_addr, rhs_.m_start_addr, 32, UVM_HEX) &
          comparer.compare_field_int("m_desired_addr",
                                     m_desired_addr, rhs_.m_desired_addr, 32, UVM_HEX) &
          comparer.compare_field_int("m_aborted",
                                     m_aborted, rhs_.m_aborted, 1, UVM_BIN));
endfunction

function void rom_ctrl_addr_force_item::abort();
  m_aborted = 1;
endfunction

function bit rom_ctrl_addr_force_item::get_aborted();
  return m_aborted;
endfunction

task rom_ctrl_addr_force_item::wait_until_aborted();
  wait(m_aborted);
endtask
