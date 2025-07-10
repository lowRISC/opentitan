// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The base class for CSR sequences, deriving from uvm_reg_sequence

class csr_base_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));
  `uvm_object_utils(csr_base_seq)

  dv_base_reg_block models[$];
  uvm_reg           all_csrs[$];
  uvm_reg           test_csrs[$];

  // By default, assume external checker (example, scoreboard) is turned off. If that is the case,
  // then writes are followed by call to predict function to update the mirrored value. Reads are
  // then checked against the mirrored value using csr_rd_check task. If external checker is
  // enabled, then we let the external checker do the predict and compare.
  // In either case, we should be able to do completely non-blocking writes and reads.
  bit external_checker = 1'b0;

  // either use num_test_csrs or {test_csr_chunk, num_csr_chunks} to test slice of all CSRs
  int num_test_csrs = 0;
  int test_csr_chunk = 1;
  int num_csr_chunks = 1;

  `uvm_object_new

  // pre_start
  virtual task pre_start();
    super.pre_start();

    // create test_csrs list only if its empty
    if (test_csrs.size() == 0) set_csr_test_range();
  endtask

  // post_start
  virtual task post_start();
    super.post_start();
    wait_no_outstanding_access();
    test_csrs.delete();
  endtask

  // extract csrs and split and prune to a specified test_csr_chunk
  virtual function void set_csr_test_range();
    int   start_idx;
    int   end_idx;
    int   chunk_size;

    // extract all csrs from the model
    all_csrs.delete();
    foreach (models[i]) begin
      models[i].get_registers(all_csrs);
    end

    void'($value$plusargs("num_test_csrs=%0d", num_test_csrs));
    if (num_test_csrs != 0) begin
      num_csr_chunks = all_csrs.size / num_test_csrs + 1;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(test_csr_chunk,
          test_csr_chunk inside {[1:num_csr_chunks]};)
    end else begin
      // extract test_csr_chunk, num_csr_chunks from plusargs
      void'($value$plusargs("test_csr_chunk=%0d", test_csr_chunk));
      void'($value$plusargs("num_csr_chunks=%0d", num_csr_chunks));
    end

    if (!(test_csr_chunk inside {[1:num_csr_chunks]})) begin
      `uvm_fatal(`gtn, $sformatf({{"Invalid opt +test_csr_chunk=%0d, +num_csr_chunks=%0d "},
                                  {"(1 <= test_csr_chunk <= num_csr_chunks)."}},
                                  test_csr_chunk, num_csr_chunks))
    end
    chunk_size = (num_test_csrs != 0) ? num_test_csrs : (all_csrs.size / num_csr_chunks + 1);
    start_idx = (test_csr_chunk - 1) * chunk_size;
    end_idx = test_csr_chunk * chunk_size;
    if (end_idx >= all_csrs.size()) end_idx = all_csrs.size() - 1;

    test_csrs.delete();
    for (int i = start_idx; i <= end_idx; i++) begin
      test_csrs.push_back(all_csrs[i]);
      `uvm_info(`gtn, $sformatf("Testing CSR %0s, reset: 0x%0x.", all_csrs[i].get_full_name(),
                                all_csrs[i].get_mirrored_value()), UVM_HIGH)
    end
    `uvm_info(`gtn, $sformatf("Testing %0d csrs [%0d - %0d] in all supplied models.",
                              test_csrs.size(), start_idx, end_idx), UVM_MEDIUM)
    test_csrs.shuffle();
  endfunction

  // check if this csr/fld is excluded from test based on the excl info in blk.csr_excl
  function bit is_excl(uvm_object obj,
                       csr_excl_type_e csr_excl_type,
                       csr_test_type_e csr_test_type);
    csr_excl_item csr_excl = get_excl_item(obj);
    if (csr_excl == null) begin
      return 0;
    end else begin
      return csr_excl.is_excl(obj, csr_excl_type, csr_test_type);
    end
  endfunction
endclass

