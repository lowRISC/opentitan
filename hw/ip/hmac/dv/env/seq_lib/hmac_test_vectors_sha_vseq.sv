// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read a few NIST vector format sha or hmac test vectors
// and compare the expected result
class hmac_test_vectors_sha_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_test_vectors_sha_vseq)
  `uvm_object_new

  rand bit [31:0] key[]; // random because sha256 will not calculate key
  bit hmac_en; // sha256 only
  string vector_list[] = test_vectors_pkg::sha_file_list;

  // SHA256 key will always be 256 bits.
  constraint key_c {
    key.size() == 8;
  }

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    test_vectors_pkg::test_vectors_t parsed_vectors[];

    foreach (vector_list[i]) begin
      // import function from the test_vectors_pkg to parse the sha vector file
      test_vectors_pkg::get_hash_test_vectors(vector_list[i], parsed_vectors);
      parsed_vectors.shuffle();

      // if in smoke_regression mode, to reduce the run time, we will randomly pick 2 vectors to
      // run this sequence
      if (cfg.smoke_test) parsed_vectors = parsed_vectors[0:1];

      foreach (parsed_vectors[j]) begin
        bit [TL_DW-1:0] intr_state_val;
        `uvm_info(`gfn, $sformatf("vector[%0d]: %0p", j, parsed_vectors[j]), UVM_HIGH)
        // wr init: SHA256 only. HMAC, endian swap, digest swap all disabled
        hmac_init(.hmac_en(hmac_en), .endian_swap(1'b0), .digest_swap(1'b0));

        `uvm_info(`gtn, $sformatf("%s, starting seq %0d, msg size = %0d",
                                  test_vectors_pkg::sha_file_list[i], j,
                                  parsed_vectors[j].msg_length_byte), UVM_MEDIUM)

        if ($urandom_range(0, 1) && !hmac_en) begin
          `DV_CHECK_RANDOMIZE_FATAL(this) // only key is randomized
          wr_key(key);
        end else begin
          wr_key(parsed_vectors[j].keys);
        end

        trigger_hash();

        // wr_msg is non_blocking to ensure the order of input msg
        wr_msg(parsed_vectors[j].msg, 1);

        trigger_process();

        wait(cfg.intr_vif.pins[HmacDone] === 1'b1);
        csr_rd(.ptr(ral.intr_state), .value(intr_state_val));
        csr_wr(.csr(ral.intr_state), .value(intr_state_val));
        // read digest and compare with the expected result, scb will calculate and check too
        compare_digest(parsed_vectors[j].exp_digest);
      end
    end
  endtask : body

endclass : hmac_test_vectors_sha_vseq
