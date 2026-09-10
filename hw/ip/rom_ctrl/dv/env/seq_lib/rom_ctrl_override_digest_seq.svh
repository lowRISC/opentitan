// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that sends a single rom_ctrl_kmac_rsp_force_item, overriding a digest response that
// rom_ctrl gets from kmac.

class rom_ctrl_override_digest_seq extends uvm_sequence #(rom_ctrl_kmac_rsp_force_item);
  `uvm_object_utils(rom_ctrl_override_digest_seq)

  // The single item of the sequence. Customise this to pick the digest to send.
  rand rom_ctrl_kmac_rsp_force_item m_item;

  extern function new(string name="");
  extern function void do_print(uvm_printer printer);

  extern task body();

  // Set a flag in m_item so that any driver that is driving that item will abort it immediately.
  extern function void abort();
endclass

function rom_ctrl_override_digest_seq::new(string name="");
  super.new(name);
  m_item = new("m_item");
endfunction

function void rom_ctrl_override_digest_seq::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_object("m_item", m_item);
endfunction

task rom_ctrl_override_digest_seq::body();
  start_item(m_item);
  finish_item(m_item);
  if (!m_item.get_abort()) begin
    `uvm_info(get_full_name(),
              $sformatf("Overrode digest from KMAC with 0x%0h", m_item.m_digest),
              UVM_HIGH)
  end
endtask

function void rom_ctrl_override_digest_seq::abort();
  m_item.abort();
endfunction
