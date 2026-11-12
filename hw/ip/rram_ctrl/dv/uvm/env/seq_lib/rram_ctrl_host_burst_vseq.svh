// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that performs several "host" operations by running rram_ctrl_host_vseq

class rram_ctrl_host_burst_vseq extends uvm_sequence;
  `uvm_object_utils(rram_ctrl_host_burst_vseq)

  // The number of operations that should be performed in total. Configure before starting this
  // sequence.
  int unsigned m_num_ops;

  // Should fetches be allowed in the sequences that run? Configure before starting this sequence.
  bit          m_allow_fetches;

  // The maximum number of operations to try to run in parallel. Setting this to NumOutstandingRdReq
  // gives the maximum possible parallelism.
  int unsigned m_max_num_running = NumOutstandingRdReq;

  // If this is set, no more operations will be started. Set it by calling abort().
  local bit    m_abort;

  // The RRAM register block. Set this by calling set_ral() before starting the sequence.
  local rram_ctrl_core_reg_block m_ral;

  // The base address of the host_tl interface on the bus. Set this by calling set_host_base_addr()
  // before starting the sequence.
  local uvm_reg_addr_t m_host_base_addr;

  // The sequencer for the host interface's tl_agent. Set this by calling set_host_sequencer()
  // before starting the sequence.
  local tl_sequencer m_host_sequencer;

  extern function new(string name="");

  extern virtual function void do_print(uvm_printer printer);
  extern task pre_start();
  extern task body();

  // Set the register block that the virtual sequence will configure. Call this before starting the
  // sequence.
  extern function void set_ral(rram_ctrl_core_reg_block ral);

  // Set the base address for the host_tl interface on the bus. Call this before starting the
  // sequence.
  extern function void set_host_base_addr(uvm_reg_addr_t base_addr);

  // Set the sequencer for the host_tl interface's tl_agent. Call this before starting the sequence.
  extern function void set_host_sequencer(tl_sequencer sequencer);

  // Set the abort flag, so that the vseq starts no more rram_ctrl_host_vseq sequences and just
  // allows the running ones to complete.
  extern function void abort();
endclass

function rram_ctrl_host_burst_vseq::new(string name="");
  super.new(name);
endfunction

function void rram_ctrl_host_burst_vseq::do_print(uvm_printer printer);
  super.do_print(printer);

  printer.print_field_int("m_num_ops", m_num_ops, 32);
  printer.print_field_int("m_allow_fetches", m_allow_fetches, 1);
  printer.print_field_int("m_max_num_running", m_max_num_running, 32);
  printer.print_field_int("m_abort", m_abort, 1);
  printer.print_field_int("m_host_base_addr", m_host_base_addr, $bits(m_host_base_addr));
endfunction

task rram_ctrl_host_burst_vseq::pre_start();
  if (m_ral == null) `uvm_fatal("no_ral", "m_ral not set before starting sequence.")
  if (m_host_sequencer == null) `uvm_fatal("no_sqr", "Sequence started without m_host_sequencer.")
  if (m_num_ops == 0) `uvm_fatal("no_ops", "m_num_ops is not positive: nothing to do!")
  if (m_max_num_running == 0) `uvm_fatal("zero_max", "m_max_num_running=0: cannot do anything.")

  super.pre_start();

  m_abort = 0;
endtask

task rram_ctrl_host_burst_vseq::body();
  int unsigned budget = m_num_ops;
  int unsigned num_running;

  `uvm_info("start_host_burst",
            $sformatf("Starting burst of %0d host_tl operations.", m_num_ops),
            UVM_MEDIUM)

  fork : isolation_fork begin
    while (budget > 0) begin
      rram_ctrl_host_vseq host_vseq = rram_ctrl_host_vseq::type_id::create("host_vseq");
      host_vseq.set_ral(m_ral);
      host_vseq.set_host_base_addr(m_host_base_addr);
      host_vseq.set_host_sequencer(m_host_sequencer);

      budget--;

      wait(num_running < m_max_num_running);

      if (m_abort) break;

      if (!host_vseq.randomize() with { !local::m_allow_fetches -> !m_fetch; }) begin
        `uvm_fatal("rand_failed", "Failed to randomize host_vseq.")
      end

      num_running++;
      fork begin
        host_vseq.start(null);
        num_running--;
      end join_none
    end
    wait fork;
  end join
endtask

function void rram_ctrl_host_burst_vseq::set_ral(rram_ctrl_core_reg_block ral);
  m_ral = ral;
endfunction

function void rram_ctrl_host_burst_vseq::set_host_base_addr(uvm_reg_addr_t base_addr);
  m_host_base_addr = base_addr;
endfunction

function void rram_ctrl_host_burst_vseq::set_host_sequencer(tl_sequencer sequencer);
  m_host_sequencer = sequencer;
endfunction

function void rram_ctrl_host_burst_vseq::abort();
  m_abort = 1;
endfunction
