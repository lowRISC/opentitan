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

  extern function new (string name="");

  extern virtual task body();

  // Write a random value to csr, after applying any write exclusion that has been defined for the
  // register.
  extern local task randomize_register(uvm_reg csr);

  // Write random values to each register in the list, running the sequences in parallel for maximum
  // throughput.
  extern local task randomize_registers(const ref uvm_reg registers[$]);

  // Read back csr using csr_rd_check and checking against the register model. Mask the comparison
  // using get_mask_excl_fields (to avoid checking the values of fields that are not modelled).
  extern local task read_back_register(uvm_reg csr);

  // Read back every register in the list, using csr_rd_check and checking against the register
  // model.
  //
  // Comparisons are masked using get_mask_excl_fields (to avoid checking the values of fields that
  // are not modelled).
  extern local task read_back_registers(uvm_reg registers[$]);

  // Write random values to each register in write_list, then read all the registers in read_list
  extern local task test_chunk(uvm_reg write_list[$], uvm_reg read_list[$]);

  // Return a random sample from reg_queue with length sample_size (or the entire list if there
  // aren't that many items)
  extern local function reg_queue_t sample_reg_list(int unsigned      sample_size,
                                                    const ref uvm_reg reg_queue[$]);
endclass

function csr_aliasing_seq::new (string name="");
    super.new(name);
endfunction

task csr_aliasing_seq::body();
  uvm_reg      total_list[$];
  int unsigned num_chunks;

  foreach(test_csrs[i]) begin
    if (!is_excl(test_csrs[i], CsrExclWrite, CsrAliasingTest)) begin
      total_list.push_back(test_csrs[i]);
    end else begin
      `uvm_info(get_full_name(),
                $sformatf("Skipping register %0s because of CsrExclWrite exclusion",
                          test_csrs[i].get_full_name()),
                UVM_MEDIUM)
    end
  end

  `uvm_info(get_full_name(),
            $sformatf("Aliasing test with list of %0d registers (with a total of %0d visible)",
                      test_csrs.size(),
                      all_csrs.size()),
            UVM_LOW)

  num_chunks = (test_csrs.size() + m_chunk_size - 1) / m_chunk_size;

  for (int unsigned i = 0; i < num_chunks; i++) begin
    int unsigned start_idx = i * m_chunk_size;
    int unsigned end_idx = start_idx + m_chunk_size;
    uvm_reg write_regs[$];

    if (end_idx >= test_csrs.size()) begin
      end_idx = test_csrs.size() - 1;
    end

    write_regs = test_csrs[start_idx:end_idx];

    `uvm_info(get_full_name(),
              $sformatf("Testing aliasing with chunk %0d/%0d", i + 1, num_chunks),
              UVM_LOW)
    foreach (write_regs[j]) begin
      `uvm_info(get_full_name(), $sformatf("  - %0s", write_regs[j].get_name()), UVM_MEDIUM)
    end

    test_chunk(write_regs, sample_reg_list(100, all_csrs));
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

task csr_aliasing_seq::randomize_registers(const ref uvm_reg registers[$]);
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

task csr_aliasing_seq::read_back_registers(uvm_reg registers[$]);
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
  randomize_registers(write_list);
  read_back_registers(read_list);
endtask

function reg_queue_t csr_aliasing_seq::sample_reg_list(int unsigned      sample_size,
                                                       const ref uvm_reg reg_queue[$]);
  uvm_reg ret[$] = reg_queue;
  ret.shuffle();
  return (reg_queue.size() < sample_size) ? ret[0:sample_size - 1] : ret;
endfunction
