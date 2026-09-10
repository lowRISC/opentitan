// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// For each CSR, this sequence writes a random value to it and reads ALL CSRs back. The read value
// of the CSR that was written is checked for correctness while adhering to its access policies. The
// read value of all other CSRs are compared against their previous values. This verifies that there
// is no aliasing across the address bits within the valid CSR space.

class csr_aliasing_seq extends csr_base_seq;
  `uvm_object_utils(csr_aliasing_seq)

  // A queue of uvm_reg objects
  typedef uvm_reg reg_queue_t[$];

  // The size of "register chunk" to use in the test.
  //
  // The list of CSRs to test (test_csrs) is checked in chunks of this size (writing a random value
  // to each register in a chunk, then reading back every register in the design to check that there
  // was no aliasing).
  int unsigned m_chunk_size = 10;

  // The number of registers to read after writing a chunk of registers, looking for values that
  // have changed unexpectedly.
  int unsigned m_reads_per_chunk = 100;

  extern function new(string name="");
  extern task body();

  // Write a random value to csr, after applying any write exclusion that has been defined for the
  // register.
  extern local task randomize_register(uvm_reg csr);

  // Write random values to each register in the list, running the sequences in parallel for maximum
  // throughput.
  extern local task randomize_chunk(const ref uvm_reg registers[$]);

  // Read back csr using csr_rd_check and checking against the register model. Mask the comparison
  // using get_mask_excl_fields (to avoid checking the values of fields that are not modelled).
  extern local task read_back_register(uvm_reg csr);

  // Read back every register in the list, using csr_rd_check and checking against the register
  // model.
  //
  // Comparisons are masked using get_mask_excl_fields (to avoid checking the values of fields that
  // are not modelled).
  extern local task read_back_chunk(uvm_reg registers[$]);

  // Write random values to each register in write_list, then read all the registers in read_list
  extern local task test_chunk(uvm_reg write_list[$], uvm_reg read_list[$]);

  // Return a random subset of reg_queue with m_reads_per_chunk registers (or the entire list if
  // there aren't that many)
  extern local function reg_queue_t sample_reg_list(const ref uvm_reg reg_queue[$]);
endclass

function csr_aliasing_seq::new(string name="");
    super.new(name);
endfunction

task csr_aliasing_seq::body();
  uvm_reg      total_list[$];
  int unsigned num_chunks;

  // The subset of test_csrs consisting of registers that do not have the CsrExclWrite exclusion.
  // This will be split into chunks of size m_chunk_size.
  uvm_reg regs_to_write[$];

  // The subset of test_csrs consisting of registers that do not have the CsrExclInitCheck or
  // CsrExclWriteCheck exclusion. Since test_csrs is just a section of all_csrs, this list is
  // probably much larger than regs_to_write.
  //
  // A random sample of m_reads_per_chunk of these registers will be read back for each chunk.
  uvm_reg regs_to_read[$];

  foreach(test_csrs[i]) begin
    if (!is_excl(test_csrs[i], CsrExclWrite, CsrAliasingTest)) begin
      regs_to_write.push_back(test_csrs[i]);
    end
  end
  foreach (all_csrs[i]) begin
    if (!(is_excl(test_csrs[i], CsrExclInitCheck, CsrAliasingTest) ||
          is_excl(test_csrs[i], CsrExclWriteCheck, CsrAliasingTest))) begin
      regs_to_read.push_back(test_csrs[i]);
    end
  end

  `uvm_info(get_full_name(),
            $sformatf({"Aliasing test with list of %0d writable and %0d readable registers ",
                       "(from a group of %0d registers selected from the %0d that are visible)"},
                      regs_to_write.size(), regs_to_read.size(),
                      test_csrs.size(), all_csrs.size()),
            UVM_LOW)

  // The test will break the registers that get written into chunks, of size m_chunk_size.
  num_chunks = (regs_to_write.size() + m_chunk_size - 1) / m_chunk_size;

  for (int unsigned i = 0; i < num_chunks; i++) begin
    // The [start_idx:end_idx] range is [i*m_chunk_size, (i+1)*m_chunk_size - 1], intersected with
    // the set of valid indices for regs_to_write.
    int unsigned start_idx = i * m_chunk_size;
    int unsigned end_idx = start_idx + m_chunk_size - 1;

    if (end_idx >= regs_to_write.size()) begin
      end_idx = regs_to_write.size() - 1;
    end

    `uvm_info(get_full_name(),
              $sformatf("Testing aliasing with chunk %0d/%0d", i + 1, num_chunks),
              UVM_LOW)
    for (int unsigned j = start_idx; j <= end_idx; j++) begin
      `uvm_info(get_full_name(), $sformatf("  - %0s", regs_to_write[j].get_name()), UVM_MEDIUM)
    end

    test_chunk(regs_to_write[start_idx:end_idx], sample_reg_list(regs_to_read));
  end
endtask

task csr_aliasing_seq::randomize_register(uvm_reg csr);
  uvm_reg_data_t wdata;

  if (!std::randomize(wdata)) begin
    `uvm_fatal(get_full_name(), "Failed to randomize wdata.")
  end

  wdata = get_csr_wdata_with_write_excl(csr, wdata, CsrAliasingTest);
  csr_wr(.ptr(csr), .value(wdata), .predict(!external_checker));
endtask

task csr_aliasing_seq::randomize_chunk(const ref uvm_reg registers[$]);
  fork : isolation_fork begin
    foreach (registers[i]) begin
      automatic uvm_reg _reg = registers[i];
      fork
        randomize_register(_reg);
      join_none
    end
    wait fork;
  end join
endtask

task csr_aliasing_seq::read_back_register(uvm_reg csr);
  csr_rd_check(.ptr           (csr),
               .compare       (!external_checker),
               .compare_vs_ral(1'b1),
               .compare_mask  (get_mask_excl_fields(csr, CsrExclWriteCheck, CsrAliasingTest)));
endtask

task csr_aliasing_seq::read_back_chunk(uvm_reg registers[$]);
  fork : isolation_fork begin
    foreach (registers[i]) begin
      automatic uvm_reg _reg = registers[i];
      fork
        read_back_register(_reg);
      join_none
    end
    wait fork;
  end join
endtask

task csr_aliasing_seq::test_chunk(uvm_reg write_list[$], uvm_reg read_list[$]);
  randomize_chunk(write_list);
  read_back_chunk(read_list);
endtask

function csr_aliasing_seq::reg_queue_t
  csr_aliasing_seq::sample_reg_list(const ref uvm_reg reg_queue[$]);

  uvm_reg ret[$] = reg_queue;
  ret.shuffle();
  return (reg_queue.size() < m_reads_per_chunk) ? ret[0:m_reads_per_chunk - 1] : ret;
endfunction
