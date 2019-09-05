// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read a few NIST vector format sha or hmac test vectors
// and compare the expected result
class hmac_test_vectors_sha_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_test_vectors_sha_vseq)
  `uvm_object_new

  rand bit [31:0] key[8]; // random because sha256 will not calculate key
  bit hmac_en; // sha256 only
  string vector_list[] = test_vectors_pkg::sha_file_list;

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    test_vectors_pkg::test_vectors_t parsed_vectors[];

    foreach (vector_list[i]) begin
      // import function from the test_vectors_pkg to parse the sha vector file
      test_vectors_pkg::parse_sha_hmac(hmac_en, i, parsed_vectors);

      foreach (parsed_vectors[j]) begin
        // wr init: SHA256 only. HMAC, endian swap, digest swap all disabled
        hmac_init(.hmac_en(hmac_en), .endian_swap(1'b0), .digest_swap(1'b0));

        `uvm_info(`gtn, $sformatf("%s, starting seq %0d, msg size = %0d",
                                  test_vectors_pkg::sha_file_list[i], j,
                                  parsed_vectors[j].msg_length_byte), UVM_LOW)

        if ($urandom_range(0, 1) && !hmac_en) begin
          `DV_CHECK_RANDOMIZE_FATAL(this) // only key is randomized
          wr_key(key);
        end else begin
          wr_key(parsed_vectors[j].keys);
        end

        trigger_hash();

        wr_msg(parsed_vectors[j].msg);

        trigger_process();

        // fifo_full intr can be triggered at the latest two cycle after process
        // example: current fifo_depth=(14 words + 2 bytes), then wr last 4 bytes, design will
        // process the 15th word then trigger intr_fifo_full
        cfg.clk_rst_vif.wait_clks(2);
        clear_intr_fifo_full();

        wait(cfg.intr_vif.pins[HmacDone] === 1'b1);
        check_interrupts(.interrupts((1 << HmacDone)), .check_set(1'b1));
        // read digest and compare with the expected result, scb will calculate and check too
        compare_digest(parsed_vectors[j].exp_digest);
      end
    end
  endtask : body

endclass : hmac_test_vectors_sha_vseq
