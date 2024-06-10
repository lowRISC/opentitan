// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read a few NIST vector format sha or hmac test vectors
// and compare the expected result
class hmac_test_vectors_sha_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_test_vectors_sha_vseq)
  `uvm_object_new
  // TODO (#22932): remove this and use the constraints from hmac_base_vseq once
  // this test is adapted for all digest sizes and key lengths
  rand bit [5:0]  key_length;
  rand bit [3:0]  digest_size;

  string vector_list[] = test_vectors_pkg::sha_file_list;

  constraint hmac_disabled_c {
    soft hmac_en == 0;
  }

  // TODO (#22932): remove this constraint and use the constraints from hmac_base_vseq once
  // this test is adapted for all digest sizes and key lengths
  constraint key_length_c {
    key_length == 'h2;  // test only with key_256
    // $countones(key_length) == 1 dist {
    //   1 :/ 8,  // Key_128/Key_256/Key_384/Key_512/Key_1024/Key_None
    //   0 :/ 2   // Illegal -> should get casted to Key_None in HW
    // };
  }

  constraint digest_size_c {
    digest_size == 'h1;  // test only with SHA2-256
    // $countones(digest_size) == 1 dist {
    //   1 :/ 8,  // SHA2_256/SHA2_384/SHA2_512/SHA2_None
    //   0 :/ 2   // Illegal -> should get casted to SHA2_None in HW
    // };
  }

  virtual task pre_start();
    cfg.save_and_restore_pct  = 0;    // Should not be triggered for this test
    do_hmac_init              = 1'b0;
    super.pre_start();
  endtask

  task body();
    test_vectors_pkg::test_vectors_t parsed_vectors[];

    foreach (vector_list[i]) begin
      // import function from the test_vectors_pkg to parse the sha vector file
      test_vectors_pkg::get_hash_test_vectors(.test_name(vector_list[i]),
                                              .parsed_vectors(parsed_vectors),
                                              .reverse_key(0));
      parsed_vectors.shuffle();

      // if in smoke_regression mode, to reduce the run time, we will randomly pick 2 vectors to
      // run this sequence
      if (cfg.smoke_test) begin
        parsed_vectors = parsed_vectors[0:1];
      end

      foreach (parsed_vectors[j]) begin
        bit [TL_DW-1:0] intr_state_val;
        `uvm_info(`gfn, $sformatf("vector[%0d]: %0p", j, parsed_vectors[j]), UVM_LOW)
        // wr init: SHA256 only. HMAC, endian swap, digest swap all disabled.
        hmac_init(.hmac_en(hmac_en), .endian_swap(1'b1), .digest_swap(1'b0), .key_swap(1'b0),
                  .digest_size(digest_size), .key_length(key_length));

        `uvm_info(`gtn, $sformatf("%s, starting seq %0d/%0d, message size %0d bits",
                  vector_list[i], j+1, parsed_vectors.size(), parsed_vectors[j].msg_length_byte*8),
                  UVM_LOW)
        `uvm_info(`gfn, $sformatf("digest size=%s, key length=%0d",
                  get_digest_size(digest_size), get_key_length(key_length)), UVM_LOW)

        // always start off the transaction by reading previous digest to clear
        // cfg.wipe_secret_triggered flag and update the exp digest val in scb with last digest
        rd_digest();

        if ($urandom_range(0, 1) && !hmac_en) begin
          `DV_CHECK_RANDOMIZE_FATAL(this) // only key is randomized
          wr_key(key);
        end else begin
          wr_key(parsed_vectors[j].keys);
        end

        trigger_hash();

        // wr_msg is non_blocking to ensure the order of input msg
        wr_msg(parsed_vectors[j].msg);

        trigger_process();

        wait(cfg.intr_vif.pins[HmacDone] === 1'b1);
        csr_rd(.ptr(ral.intr_state), .value(intr_state_val));
        csr_wr(.ptr(ral.intr_state), .value(intr_state_val));
        // read digest and compare with the expected result, scb will calculate and check too
        compare_digest(parsed_vectors[j].exp_digest, digest_size);   // TODO (#23288)
      end
    end
  endtask : body

endclass : hmac_test_vectors_sha_vseq
