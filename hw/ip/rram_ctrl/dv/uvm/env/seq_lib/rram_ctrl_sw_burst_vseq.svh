// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that performs several SW operations by running rram_ctrl_sw_vseq

class rram_ctrl_sw_burst_vseq extends uvm_sequence;
  `uvm_object_utils(rram_ctrl_sw_burst_vseq)

  // The number of words that should be read/written/rewritten in total. Configure it before
  // starting this sequence.
  int unsigned m_num_words;

  // A status that accumulates the results of all the register transactions in the child sequences.
  // When start finishes, it will either be UVM_IS_OK (if everything worked) or UVM_NOT_OK (if
  // anything failed responded with an error code).
  uvm_status_e m_status = UVM_IS_OK;

  // If this bit is set, the body will abort: telling any child vseq that it's running to abort and
  // then completing with m_status = UVM_NOT_OK when that finishes. Set this by calling abort().
  local bit m_abort;

  // The RRAM register block. Set this by calling set_ral() before starting the sequence.
  local rram_ctrl_core_reg_block m_ral;

  extern function new(string name="");

  extern virtual function void do_print(uvm_printer printer);
  extern task pre_start();
  extern task body();

  // Abort this sequence, which means that it will abort any rram_ctrl_sw_vseq that it's currently
  // running and complete (with m_status = UVM_NOT_OK) as soon as that finishes.
  extern function void abort();

  // Set the register block that the virtual sequence will configure. Call this before starting the
  // sequence.
  extern function void set_ral(rram_ctrl_core_reg_block ral);
endclass

function rram_ctrl_sw_burst_vseq::new(string name="");
  super.new(name);
endfunction

function void rram_ctrl_sw_burst_vseq::do_print(uvm_printer printer);
  string status_name = (m_status.name() == "") ? "??" : m_status.name();

  super.do_print(printer);

  printer.print_field_int("m_num_words", m_num_words, 32);
  printer.print_generic("m_status", "uvm_status_e", $bits(m_status),
                        $sformatf("%0s (0x%0h)", status_name, m_status));
  printer.print_field_int("m_abort", m_abort, 1);
endfunction

task rram_ctrl_sw_burst_vseq::pre_start();
  if (m_ral == null) `uvm_fatal("no_ral", "m_ral not set before starting sequence.")
  if (m_num_words == 0) `uvm_fatal("no_words", "m_num_words is not positive: nothing to do!")
  m_abort = 0;

  super.pre_start();
endtask

task rram_ctrl_sw_burst_vseq::body();
  int unsigned budget = m_num_words;

  `uvm_info("start_burst",
            $sformatf("Starting burst of SW operations to address %0d words in total.",
                      m_num_words),
            UVM_MEDIUM)

  while (budget > 0) begin
    rram_ctrl_sw_vseq sw_vseq = rram_ctrl_sw_vseq::type_id::create("sw_vseq");
    sw_vseq.set_ral(m_ral);

    if (!sw_vseq.randomize() with { m_num + 1 <= budget; }) begin
      `uvm_fatal("rand_failed", "Failed to randomize sw_vseq.")
    end

    if (sw_vseq.m_num >= budget) begin
      `uvm_fatal("over_bound", "Randomisation didn't constrain m_num below budget.")
    end

    budget -= sw_vseq.m_num + 1;

    // Run sw_vseq, but wait for m_abort to be set. If so, tell sw_vseq to abort and then wait for
    // it to finish.
    fork : isolation_fork begin
      fork
        sw_vseq.start(null);
        begin
          wait(m_abort);
          sw_vseq.abort();
          wait(0);
        end
      join_any
      disable fork;
    end join

    if (m_abort || sw_vseq.m_status != UVM_IS_OK) begin
      m_status = UVM_NOT_OK;
      break;
    end
  end
endtask

function void rram_ctrl_sw_burst_vseq::abort();
  m_abort = 1;
endfunction

function void rram_ctrl_sw_burst_vseq::set_ral(rram_ctrl_core_reg_block ral);
  m_ral = ral;
endfunction
