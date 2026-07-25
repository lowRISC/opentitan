// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that can be driven by a rom_ctrl_kmac_rsp_force_driver to override the value of a
// kmac response.

class rom_ctrl_kmac_rsp_force_item extends uvm_sequence_item;
  `uvm_object_utils(rom_ctrl_kmac_rsp_force_item)

  // The digest value to use (overriding the XOR of the digest_s0 and digest_s1 fields of the
  // app_rsp_t)
  //
  // Note that this represents the digest itself (which is the most convenient data type for other
  // code). Forcing the signal will only actually force the bottom TopCount 32-bit words. The upper
  // bits of this value will have no effect.
  rand bit [kmac_pkg::AppDigestW-1:0] m_digest;

  // A flag saying that the override should be aborted. Set this by calling abort(); read it with
  // get_abort(); wait for it to be true by calling wait_until_abort().
  local bit m_abort;

  extern function new(string name = "");
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  // Set the m_abort flag, causing calls to wait_abort to complete.
  extern function void abort();

  // Return true if abort() has been called. Wait for that to happen with wait_until_abort().
  extern function bit get_abort();

  // Wait until m_abort is set (by someone calling abort). Safe to kill.
  extern task wait_until_abort();
endclass

function rom_ctrl_kmac_rsp_force_item::new(string name = "");
  super.new(name);
endfunction

function void rom_ctrl_kmac_rsp_force_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field("m_digest", m_digest, kmac_pkg::AppDigestW, UVM_HEX);
  printer.print_field_int("m_abort", m_abort, 1, UVM_BIN);
endfunction

function void rom_ctrl_kmac_rsp_force_item::do_copy(uvm_object rhs);
  rom_ctrl_kmac_rsp_force_item rhs_;
  if (rhs == null) `uvm_fatal("do_copy", "Cannot copy from RHS: it is null.")
  if (!$cast(rhs_, rhs)) `uvm_fatal("do_copy", "Cannot cast RHS: wrong type?")

  super.do_copy(rhs);
  m_digest = rhs_.m_digest;
  m_abort = rhs_.m_abort;
endfunction

function bit rom_ctrl_kmac_rsp_force_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  rom_ctrl_kmac_rsp_force_item rhs_;

  if (rhs == null || !$cast(rhs_, rhs)) begin
    comparer.print_msg("RHS is null or is not a rom_ctrl_kmac_rsp_force_item.");
    return 0;
  end

  return (super.do_compare(rhs, comparer) &
          comparer.compare_field("m_digest", m_digest, rhs_.m_digest,
                                 kmac_pkg::AppDigestW, UVM_HEX) &
          comparer.compare_field_int("m_abort", m_abort, rhs_.m_abort, 1, UVM_BIN));
endfunction

function void rom_ctrl_kmac_rsp_force_item::abort();
  m_abort = 1;
endfunction

function bit rom_ctrl_kmac_rsp_force_item::get_abort();
  return m_abort;
endfunction

task rom_ctrl_kmac_rsp_force_item::wait_until_abort();
  wait(m_abort);
endtask
