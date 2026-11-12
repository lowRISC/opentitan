// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that writes repeatedly to the RRAM write FIFO

class rram_ctrl_fifo_write_vseq extends uvm_sequence;
  `uvm_object_utils(rram_ctrl_fifo_write_vseq)

  // The number of words to write to the FIFO. This should be set by the caller before starting the
  // sequence.
  int unsigned m_num_words;

  // A status that accumulates the results of all the register transactions in the sequence. When
  // start finishes, it will either be UVM_IS_OK (if everything worked) or UVM_NOT_OK (if anything
  // failed).
  uvm_status_e m_status = UVM_IS_OK;

  // If this bit is set, the body will abort, completing with m_status = UVM_NOT_OK as soon as any
  // register operation finishes. Set this by calling abort().
  local bit m_abort;

  // The memory representing the FIFO. (Since it is a 1-element window, the sequence will always
  // write to its first address). Set this by calling set_window() before starting the sequence.
  local uvm_mem m_window;

  extern function new(string name="");

  extern virtual function void do_print(uvm_printer printer);
  extern task pre_start();
  extern task body();

  // Abort this sequence so that it stops running register operations and returns with m_status set
  // to UVM_NOT_OK as soon as the currently running operation finishes.
  extern function void abort();

  // Set the register block that the virtual sequence will configure. Call this before starting the
  // sequence.
  extern function void set_window(uvm_mem window);
endclass

function rram_ctrl_fifo_write_vseq::new(string name="");
  super.new(name);
endfunction

function void rram_ctrl_fifo_write_vseq::do_print(uvm_printer printer);
  string status_name = (m_status.name() == "") ? "??" : m_status.name();

  super.do_print(printer);
  printer.print_field_int("m_num_words", m_num_words, 32);
  printer.print_generic("m_status", "uvm_status_e", $bits(m_status),
                        $sformatf("%0s (0x%0h)", status_name, m_status));
endfunction

task rram_ctrl_fifo_write_vseq::pre_start();
  if (m_window == null) `uvm_fatal("no_window", "m_window has not been set.")
  m_abort = 0;

  super.pre_start();
endtask

task rram_ctrl_fifo_write_vseq::body();
  for (int unsigned i = 0; i < m_num_words; i++) begin
    bit [31:0]   wdata;
    uvm_status_e txn_status;

    if (!std::randomize(wdata)) `uvm_fatal("rand_failed", "Failed to randomize wdata.")

    m_window.write(txn_status, 0, wdata);
    if (m_abort || txn_status != UVM_IS_OK) begin
      m_status = UVM_NOT_OK;
      return;
    end
  end
endtask

function void rram_ctrl_fifo_write_vseq::abort();
  m_abort = 1;
endfunction

function void rram_ctrl_fifo_write_vseq::set_window(uvm_mem window);
  m_window = window;
endfunction
