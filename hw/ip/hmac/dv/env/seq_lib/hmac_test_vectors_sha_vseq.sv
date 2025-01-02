// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read SHA-2 NIST vectors and compare computed results with the expected values
// https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing

class hmac_test_vectors_sha_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_test_vectors_sha_vseq)

  string vector_list_256[] = test_vectors_pkg::sha2_256_file_list;
  string vector_list_384[] = test_vectors_pkg::sha2_384_file_list;
  string vector_list_512[] = test_vectors_pkg::sha2_512_file_list;

  string digest_size_arg;

  // Constraints
  extern constraint hmac_disabled_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task pre_start();
  extern task body();

  // Class specific methods
  extern task feed_vectors (string vector_list[], bit [3:0] digest_size);
endclass : hmac_test_vectors_sha_vseq


constraint hmac_test_vectors_sha_vseq::hmac_disabled_c {
  soft hmac_en == 0;
}

function hmac_test_vectors_sha_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_test_vectors_sha_vseq::pre_start();
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
endtask : pre_start

task hmac_test_vectors_sha_vseq::feed_vectors (string vector_list[], bit [3:0] digest_size);
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

      case (parsed_vectors[j].sha2_key_length)
        128:     key_length = Key_128;
        256:     key_length = Key_256;
        384:     key_length = Key_384;
        512:     key_length = Key_512;
        1024:    key_length = Key_1024;
        default: key_length = Key_None;
      endcase

      // only input HMAC test vectors with valid key length and while key length is
      // not 1024-bit for SHA-2 256 to avoid invalid configuration case
      if ((!hmac_en) || (hmac_en &&
                        (key_length!= Key_None) &&
                        !(digest_size == SHA2_256 && key_length == Key_1024))) begin
        hmac_init(.hmac_en(hmac_en), .endian_swap(1'b1), .digest_swap(1'b0), .key_swap(1'b0),
                  .digest_size(digest_size), .key_length(key_length));

        `uvm_info(`gtn, $sformatf("%s, starting seq %0d/%0d, message size %0d bits",
                  vector_list[i], j+1, parsed_vectors.size(),
                  parsed_vectors[j].msg_length_byte*8),
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
        compare_digest(parsed_vectors[j].exp_digest,
                       parsed_vectors[j].digest_length_byte,
                       digest_size);
      end else begin
        `uvm_info(`gtn, $sformatf("Discarding HMAC seq with invalid key length"), UVM_LOW)
        continue;
      end
    end
  end
endtask : feed_vectors

task hmac_test_vectors_sha_vseq::body();
  string vector_list[];
  if (digest_size_arg == "SHA2_256") begin
    digest_size = SHA2_256;
    vector_list = vector_list_256;
  end else if (digest_size_arg == "SHA2_384") begin
    digest_size = SHA2_384;
    vector_list = vector_list_384;
  end else if (digest_size_arg == "SHA2_512") begin
    digest_size = SHA2_512;
    vector_list = vector_list_512;
  end else begin
    `uvm_fatal(`gfn, {"Digest size is not recognized, please use command-line argument as: ",
                      "sha2_digest_size=SHA2_256/SHA2_384/SHA2_512 or don't pass this argument"})
  end
  `uvm_info(`gfn, $sformatf("Starting SHA-2/HMAC %s NIST test vectors...",
            digest_size_arg), UVM_LOW)
  feed_vectors (vector_list, digest_size);
endtask : body
