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
//     If max_num_test_csrs has been set to a positive number after creating the sequence, it is
//     used as another upper bound on the number of CSRs in a chunk for the sequence.
//
//  +num_csr_chunks=, +test_csr_chunk=
//
//     If num_test_csrs is not provided, the list of CSRs in all_csrs can instead be divided into a
//     requested number of contiguous chunks by setting num_csr_chunks. The index of the chunk to
//     test is then provided with test_csr_chunk.
//
//     It is an error to use these flags if max_num_test_csrs is set to a positive number (because
//     there's not a nice description of the length of chunks in that situation).

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

  // An upper bound on the number of CSRs that are tested by this sequence. It can be set by the
  // creator before starting the sequence. If not overridden, this will be zero (meaning there is no
  // upper bound).
  int unsigned max_num_test_csrs;

  // A queue of all the CSR registers found in register blocks in models.
  protected uvm_reg all_csrs[$];

  // A queue of the CSR registers that have been selected for this test. These are contained in
  // all_csrs, but may be a proper subset if set_csr_test_range has picked only some of them (as
  // instructed by the max_num_test_csrs or the num_test_csrs or num_csr_chunks plusargs). They will
  // also be shuffled into a random order.
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

  // Create test_csrs list only if it is empty. Note that this won't actually do anything if the
  // entries in the models array don't have any registers.
  if (test_csrs.size() == 0) begin
    set_csr_test_range();
  end
endtask

task csr_base_seq::post_start();
  super.post_start();
  wait_no_outstanding_access();
  test_csrs.delete();
endtask

function void csr_base_seq::set_csr_test_range();
  bit has_ntc, has_ncc, has_tcc;

  int unsigned num_csrs;
  int          num_test_csrs, num_csr_chunks, test_csr_chunk;

  int unsigned start_idx, end_idx;

  // extract all csrs from the model
  all_csrs.delete();
  foreach (models[i]) begin
    models[i].get_registers(all_csrs);
  end

  num_csrs = all_csrs.size();
  if (!num_csrs) return;

  // Has the num_test_csrs plusarg been supplied to give the maximum size of a chunk?
  if ($value$plusargs("num_test_csrs=%0d", num_test_csrs)) begin
    // Check that the user hasn't requested chunks of less than one: that wouldn't make much sense.
    // Generate a UVM error and ignore the plusarg.
    if (num_test_csrs < 1) begin
      `uvm_error(`gtn, $sformatf("+num_test_csrs=%0d, which is not positive.", num_test_csrs))
    end else begin
      has_ntc = 1;

      // If num_test_csrs is greater than the total number of CSRs, clip it to what is available.
      if (num_test_csrs > num_csrs) begin
        num_test_csrs = num_csrs;
      end
    end
  end

  // Has the num_csr_chunks plusarg been supplied?
  if ($value$plusargs("num_csr_chunks=%0d", num_csr_chunks)) begin
    // Check that we want a positive number of CSR chunks (since "splitting the list into -3 chunks"
    // wouldn't make much sense!). If not, generate a UVM error and ignore the plusarg.
    if (num_csr_chunks < 1) begin
      `uvm_error(`gtn, $sformatf("+num_csr_chunks=%0d, which is not positive.", num_csr_chunks))
    end else begin
      has_ncc = 1;
    end
  end

  // Has the test_csr_chunk plusarg been supplied?
  if ($value$plusargs("test_csr_chunk=%0d", test_csr_chunk)) begin
    if (!has_ncc) begin
      // This argument only makes sense if we *have* specified a number of CSR chunks.
      `uvm_error(`gtn, "Cannot supply test_csr_chunk without num_csr_chunks")
    end else if (test_csr_chunk < 0 || test_csr_chunk >= num_csr_chunks) begin
      // Similarly, it only makes sense if it's a valid index into the list of chunks.
      `uvm_error(`gtn,
                 $sformatf("+test_csr_chunk=%0d is invalid when num_csr_chunks=%0d",
                           test_csr_chunk, num_csr_chunks));
    end
    has_tcc = 1;
  end

  // Check that num_test_csrs and num_csr_chunks haven't both been supplied (because then there
  // isn't any good chunk size)
  if (has_ntc && has_ncc) begin
    `uvm_error(`gtn, "Cannot set both +num_csr_chunks and +num_test_csrs. Using the latter.")
    has_ncc = 0;
  end

  // At this point, at most one of has_ntc and has_ncc is true.
  if (has_ncc) begin
    int unsigned chunk_idx;

    // If num_csr_chunks has been supplied we can use it to derive a chunk size in the same way as
    // the has_ntc case.
    int unsigned chunk_size = (num_csrs + num_csr_chunks - 1) / num_csr_chunks;

    // At this point, we might find that the requested number of chunks is incompatible with
    // max_num_test_csrs. If so, generate an error and then clip chunk_size (to ensure the test
    // doesn't run for a silly time)
    if (max_num_test_csrs > 0 && chunk_size > max_num_test_csrs) begin
      `uvm_error(`gtn,
                 $sformatf("chunk_size %0d is too large for max_num_test_csrs %0d",
                           chunk_size, max_num_test_csrs))
      chunk_size = max_num_test_csrs;
    end

    // We might already have a chunk index in test_csr_chunk. If not, we pick one at random in the
    // allowed range.
    chunk_idx = has_tcc ? test_csr_chunk : $urandom_range(num_csr_chunks - 1);

    // Again, convert these two into a pair of CSR indices (where end_idx is strictly past the end)
    start_idx = chunk_idx * chunk_size;
    end_idx = start_idx + chunk_size - 1;
  end else if (has_ntc || max_num_test_csrs > 0) begin
    int unsigned num_chunks, chunk_size, chunk_idx;

    // Take the smaller supplied value of num_test_csrs and max_num_test_csrs to give an upper bound
    // on the size of a chunk.
    int unsigned max_chunk_size;
    if (max_num_test_csrs > 0) begin
      if (has_ntc) begin
        max_chunk_size = (max_num_test_csrs < num_test_csrs) ? max_num_test_csrs : num_test_csrs;
      end else begin
        max_chunk_size = max_num_test_csrs;
      end
    end else begin
      max_chunk_size = num_test_csrs;
    end

    // Now divide the total number of CSRs by that bound. Rounding up gives enough chunks to be able
    // to cover the whole list.
    num_chunks = (num_csrs + max_chunk_size - 1) / max_chunk_size;

    // Given the number of chunks, we can now divide the number of CSRs by that to get the size of a
    // chunk. Note that this will be at most max_chunk_size but may be much smaller.
    //
    // For example, if max_chunk_size = 50 and num_csrs = 51 then we will get 2 = ceil(51/50) chunks
    // but then assign ceil(51/2) = 26 tests to each chunk, which gets "maximum parallelism" by
    // avoiding dramatic differences between the size of chunks.
    chunk_size = (num_csrs + num_chunks - 1) / num_chunks;

    // Pick a chunk index (less than num_chunks) at random
    chunk_idx = $urandom_range(num_chunks - 1);

    // Finally, convert that into a pair of CSR indices (where end_idx is strictly past the end)
    start_idx = chunk_idx * chunk_size;
    end_idx = start_idx + chunk_size - 1;
  end else begin
    // If neither value was provided, we work on the entire list of CSRs at once.
    start_idx = 0;
    end_idx = num_csrs - 1;
  end

  // At this point, start_idx and end_idx should have been chosen, with start_idx < end_idx. Convert
  // the end index to an inclusive limit, by clipping to the number of CSRs.
  end_idx = (end_idx >= num_csrs) ? num_csrs - 1 : end_idx;

  // At this point, we should have 0 <= start_idx <= end_idx < num_csrs. If that isn't true, there
  // was a bug in the code above.
  `DV_CHECK_FATAL(start_idx <= end_idx && end_idx < num_csrs)

  // Replace any existing list of CSRs with the chosen chunk in a random order.
  test_csrs.delete();
  for (int i = start_idx; i <= end_idx; i++) begin
    test_csrs.push_back(all_csrs[i]);
    `uvm_info(`gtn, $sformatf("Testing CSR %0s, reset: 0x%0x.", all_csrs[i].get_full_name(),
                              all_csrs[i].get_mirrored_value()), UVM_HIGH)
  end
  `uvm_info(`gtn,
            $sformatf("Testing %0d csrs [%0d - %0d] from supplied models.",
                      test_csrs.size(), start_idx, end_idx),
            UVM_MEDIUM)

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
