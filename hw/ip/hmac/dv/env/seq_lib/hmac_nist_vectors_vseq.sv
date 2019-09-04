// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq will read a few NIST standard vector files and compare the expected value
class hmac_nist_vectors_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_nist_vectors_vseq)
  `uvm_object_new

  rand bit [31:0] key[8]; // random because sha256 will not calculate key

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    bit                              hmac_en = 0; // sha256 only
    nist_vectors_pkg::nist_vectors_t parsed_vectors[];

    foreach(nist_vectors_pkg::sha_file_list[i]) begin
      // import function from the nist_vectors_pkg to parse the sha vector file
      nist_vectors_pkg::parse_sha(i, parsed_vectors);

      foreach(parsed_vectors[j]) begin
        // wr init: SHA256 only. HMAC, endian swap, digest swap all disabled
        hmac_init(.hmac_en(hmac_en), .endian_swap(1'b0), .digest_swap(1'b0));

        `uvm_info(`gtn, $sformatf("%s, starting seq %0d, msg size = %0d",
                                  nist_vectors_pkg::sha_file_list[i], j,
                                  parsed_vectors[j].msg_length_byte), UVM_LOW)

        if ($urandom_range(0, 1)) begin
          `DV_CHECK_RANDOMIZE_FATAL(this) // only key is randomized
          wr_key(key);
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

        // read digest and compare with the expected NIST result, scb will calculate and check too
        compare_digest(parsed_vectors[j].exp_digest);
      end
    end
  endtask : body

endclass : hmac_nist_vectors_vseq
