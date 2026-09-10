// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a single rom_ctrl_addr_force_item, forcing rom_ctrl to skip the middle of
// ROM.

class rom_ctrl_skip_middle_seq extends uvm_sequence #(rom_ctrl_addr_force_item);
  `uvm_object_utils(rom_ctrl_skip_middle_seq)

  // The single item of the sequence. Customise this to control the start and end address of the
  // skip.
  rand rom_ctrl_addr_force_item m_item;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);

  extern task body();

  // Set a flag in m_item so that any driver that is driving that item will abort it immediately.
  extern function void abort();
endclass

function rom_ctrl_skip_middle_seq::new(string name="");
  super.new(name);
  m_item = new("m_item");
endfunction

function void rom_ctrl_skip_middle_seq::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_object("m_item", m_item);
endfunction

task rom_ctrl_skip_middle_seq::body();
  start_item(m_item);
  finish_item(m_item);

  if (m_item.get_aborted()) begin
    `uvm_info(get_full_name(), "Aborted skipping the middle of rom_ctrl count", UVM_HIGH)
  end else begin
    `uvm_info(get_full_name(),
              $sformatf("Skipped middle of rom_ctrl count (0x%0h -> 0x%0h)",
                        m_item.m_start_addr, m_item.m_desired_addr),
              UVM_HIGH)
  end
endtask

function void rom_ctrl_skip_middle_seq::abort();
  m_item.abort();
endfunction
