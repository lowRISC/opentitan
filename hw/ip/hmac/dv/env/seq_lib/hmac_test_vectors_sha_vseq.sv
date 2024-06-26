// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read SHA-2 NIST vectors and compare computed results with the expected values
// https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing

class hmac_test_vectors_sha_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_test_vectors_sha_vseq)
  `uvm_object_new

  string vector_list_256[] = test_vectors_pkg::sha2_256_file_list;
  string vector_list_384[] = test_vectors_pkg::sha2_384_file_list;
  string vector_list_512[] = test_vectors_pkg::sha2_512_file_list;

  string digest_size_arg;

  constraint hmac_disabled_c {
    soft hmac_en == 0;
  }

  virtual task pre_start();
    cfg.save_and_restore_pct  = 0;    // Should not be triggered for this test
    do_hmac_init              = 1'b0;
    // grab SHA-2 digest size from the command-line argument
    void'($value$plusargs("sha2_digest_size=%s", digest_size_arg));
    // When the command line argument is not defined then randomize the digest_size with valid data
    // This is a safety but also necessary for the stress tests as extra argument cannot be passed
    if (digest_size_arg == "") begin
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(
        digest_size,
        digest_size inside {SHA2_256, SHA2_384, SHA2_512};
      )
      digest_size_arg = get_digest_size(digest_size);
    end
    super.pre_start();
  endtask

  task feed_vectors (string vector_list[], bit [3:0] digest_size, bit [5:0] key_length);
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
        compare_digest(parsed_vectors[j].exp_digest, digest_size);
      end
    end
  endtask

  task body();
    string vector_list[];
    if (digest_size_arg == "SHA2_256") begin
      digest_size = SHA2_256;
      // TODO: fix key_length for now until we add HMAC test vectors with other key lengths
      key_length  = Key_256;
      vector_list = vector_list_256;
    end else if (digest_size_arg == "SHA2_384" && !hmac_en) begin
      // TODO (issue #22932): release the constraints to run HMAC test vectors as well
      // once HMAC test vectors with different key lengths are added
      digest_size = SHA2_384;
      key_length  = Key_256;
      vector_list = vector_list_384;
    end else if (digest_size_arg == "SHA2_512" && !hmac_en) begin
      // TODO (issue #22932): release the constraints to run HMAC test vectors as well
      // once HMAC test vectors with different key lengths are added
      digest_size = SHA2_512;
      key_length  = Key_256;
      vector_list = vector_list_512;
    // TODO (issue #22932): after merged with this PR #23771, a simple "else" could be used as
    // hmac_en condition won't be there anymore
    end else if (digest_size_arg != "SHA2_256" && digest_size_arg != "SHA2_384" &&
                 digest_size_arg != "SHA2_512") begin
      `uvm_fatal(`gfn, {"Digest size is not recognized, please use command-line argument as: ",
                        "sha2_digest_size=SHA2_256/SHA2_384/SHA2_512 or don't pass this argument"})
    end
    feed_vectors (vector_list, digest_size, key_length);
    `uvm_info(`gfn, $sformatf("Starting SHA-2/HMAC %s and %s NIST test vectors...",
              digest_size_arg, "Key_256"), UVM_LOW)
  endtask : body

endclass : hmac_test_vectors_sha_vseq
