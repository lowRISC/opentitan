// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The base class for CSR sequences, deriving from uvm_reg_sequence
//
// To use this sequence, create the object and then populate models, external_checker, and
// num_test_csrs. Run the sequence by calling the start() task.
//
// Any subclass of this sequence performs tests across a set of registers in the design. The
// complete list of available registers is computed just before the sequence body (in the pre_start
// task), but a test may wish to check a smaller subset of these registers.
//
// To make that possible, there are two plusarg-based mechanisms:
//
//  +num_test_csrs=
//
//     If num_test_csrs is a positive number, the list of CSRs in all_csrs is divided into
//     contiguous chunks of that length and then the sequence operates on some randomly chosen chunk
//     from that list.
//
//     NOTE: Overriding the plusarg, a test can set the num_test_csrs class variable after creating
//           the sequence, but before calling start(). (TODO: This seems backwards! We should
//           probably take a min somewhere instead).
//
//  +num_csr_chunks=, +test_csr_chunk=
//
//     If num_test_csrs is not provided, the list of CSRs in all_csrs can instead be divided into a
//     requested number of contiguous chunks by setting num_csr_chunks. The index of the chunk to
//     test is then provided with test_csr_chunk.

class csr_base_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));
  `uvm_object_utils(csr_base_seq)

  // A queue of register models (UVM register blocks), whose registers will be added to the lists of
  // CSRs (all_csrs and test_csrs) in pre_start.
  dv_base_reg_block models[$];

  // A flag that is true if there is some external checker (scoreboard).
  //
  // If it is false then each register write is followed by a call to that register's predict
  // function in order to update the mirrored value. Similarly, reads are checked against the
  // register's mirrored value (using the by passing a true "compare" argument to the csr_rd_check
  // task).
  //
  // If the flag is true, the sequence doesn't do predict and compare, instead leaving that to the
  // scoreboard.
  //
  // In either case, the prediction and comparison happen as part of the register write/read, which
  // means that this sequence can do completely non-blocking writes and reads.
  bit external_checker;

  // The size of chunk for the CSRs that are selected by this sequence. This is either set by the
  // creator of the sequence or can be inferred from plusargs (described above).
  int num_test_csrs = 0;

  // A queue of all the CSR registers found in register blocks in models.
  protected uvm_reg all_csrs[$];

  // A queue of the CSR registers that have been selected for this test. These are contained in
  // all_csrs, but may be a proper subset if set_csr_test_range has picked only some of them (as
  // instructed by the num_test_csrs or num_csr_chunks plusargs). They will also be shuffled into a
  // random order.
  //
  // The queue gets populated by set_csr_test_range, which is called by the pre_start task. It is
  // then cleared by post_start, to ensure that it will be re-populated if the sequence is run
  // again.
  protected uvm_reg test_csrs[$];

  extern function new (string name="");

  // The pre_start task overrides that of uvm_sequence_base.
  //
  // It is run just before the body task and is in charge of selecting a subset of all_csrs on which
  // the sequence will operate. This subset is written to test_csrs.
  extern task pre_start();

  // The post_start task overrides that of uvm_sequence_base.
  //
  // It is run just after the body task. In the body task, the sequence will have requested a stream
  // of CSR accesses, but the implementation doesn't necessarily wait for the accesses to complete.
  // To make sure they have actually done so, the post_start task waits for a period with no
  // outstanding CSR accesses (which would mean that each access is done).
  //
  // The task also clears test_csrs, which means that the same sequence can be run another time and
  // the randomisation in set_csr_test_range might pick a different set of test CSRs.
  extern task post_start();

  // Pick a subset of all_csrs and write that to test_csrs. The function's behaviour is described in
  // the comment about plusargs before the class.
  extern local function void set_csr_test_range();

  // Return true if this is a CSR or field that has been excluded from the test described in
  // csr_test_type by some exclusion (that ultimately came from the hjson register description).
  extern function bit is_excl(uvm_object obj,
                              csr_excl_type_e csr_excl_type,
                              csr_test_type_e csr_test_type);
endclass

function csr_base_seq::new (string name="");
  super.new(name);
endfunction

task csr_base_seq::pre_start();
  super.pre_start();

  // create test_csrs list only if it is empty
  if (test_csrs.size() == 0) set_csr_test_range();
endtask

task csr_base_seq::post_start();
  super.post_start();
  wait_no_outstanding_access();
  test_csrs.delete();
endtask

function void csr_base_seq::set_csr_test_range();
  int   start_idx;
  int   end_idx;
  int   chunk_size;
  int   test_csr_chunk = 1;
  int   num_csr_chunks = 1;

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

function bit csr_base_seq::is_excl(uvm_object obj,
                                   csr_excl_type_e csr_excl_type,
                                   csr_test_type_e csr_test_type);
  csr_excl_item csr_excl = get_excl_item(obj);
  if (csr_excl == null) begin
    return 0;
  end else begin
    return csr_excl.is_excl(obj, csr_excl_type, csr_test_type);
  end
endfunction
