// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_test_vectors_base_vseq extends kmac_smoke_vseq;

  `uvm_object_utils(kmac_test_vectors_base_vseq)
  `uvm_object_new

  string test_list[];

  virtual task pre_start();
    msg_c.constraint_mode(0);
    output_len_c.constraint_mode(0);
    super.pre_start();
  endtask

  task body();
    test_vectors_pkg::test_vectors_t vectors[];

    foreach (test_list[i]) begin
      // parse each test vector file
      test_vectors_pkg::get_hash_test_vectors(test_list[i], vectors);

      `uvm_info(`gfn, $sformatf("Starting %0s test vectors", test_list[i]), UVM_LOW)
      `uvm_info(`gfn, $sformatf("Preparing %0d test vectors...", vectors.size()), UVM_LOW)

      // Run a basic hash operation for each parsed test vector
      foreach (vectors[j]) begin
        // `compare_digest()` passes three arrays by reference, one of which is contained
        // inside of the vectors[j] struct.
        //
        // Hierarchical references to an array inside a struct is not supported by VCS,
        // so
        bit [7:0] exp_digest[] = vectors[j].exp_digest;
        bit [7:0] share0[];
        bit [7:0] share1[];

        `uvm_info(`gfn, $sformatf("Running test vector %0d", j), UVM_LOW)
        `uvm_info(`gfn, $sformatf("vectors[%0d]: %0p", j, vectors[j]), UVM_HIGH)

        // Use this hook to set the appropriate configuration options
        randomize_cfg(vectors[j]);

        msg = vectors[j].msg;
        `uvm_info(`gfn, $sformatf("msg: %0p", msg), UVM_HIGH)

        kmac_init();

        if (kmac_en) begin
          // set the prefix
          str_utils_pkg::str_to_bytes(vectors[j].customization_str, custom_str_arr);
          `uvm_info(`gfn,
                    $sformatf("[kmac_test_vector] custom_str: %0s",
                              vectors[j].customization_str),
                    UVM_HIGH)
          `uvm_info(`gfn,
                    $sformatf("[kmac_test_vector] custom_str_arr: %0p", custom_str_arr),
                    UVM_HIGH)
          set_prefix();

          // write the key shares
          for (int k = 0; k < KMAC_NUM_SHARES; k++) begin
            for (int l = 0; l < KMAC_NUM_KEYS_PER_SHARE; l++) begin
              if (k == 0 && l < vectors[j].key_length_word) begin
                key_share[k][l] = vectors[j].keys[l];
              end else begin
                key_share[k][l] = '0;
              end
            end
          end
          write_key_shares();
        end

        // provide entropy if masked
        if (cfg.enable_masking && entropy_mode == EntropyModeSw) begin
          provide_sw_entropy();
        end

        issue_cmd(CmdStart);

        write_msg(msg, 1);

        if (kmac_en) begin
          right_encode(xof_en ? 0 : output_len * 8, output_len_enc);
          write_msg(output_len_enc, 1);
        end

        issue_cmd(CmdProcess);

        wait_for_kmac_done();

        read_digest_shares(output_len, cfg.enable_masking, share0, share1);

        `uvm_info(`gfn, $sformatf("share0: %0p", share0), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("share1: %0p", share1), UVM_HIGH)

        issue_cmd(CmdDone);

        compare_digest(exp_digest, share0, share1, cfg.enable_masking);
      end
    end
  endtask

  // This function is used to randomize the KMAC settings
  // based on the test vector config
  virtual function void randomize_cfg(test_vectors_pkg::test_vectors_t vector);
    `uvm_fatal(`gfn, "Should not be called in the base class")
  endfunction

  virtual function void compare_digest(const ref bit [7:0] exp_digest[],
                                       const ref bit [7:0] act_share0[],
                                       const ref bit [7:0] act_share1[],
                                       input bit en_masking);
    bit [7:0] act_digest[] = new[output_len];

    for (int i = 0; i < output_len; i++) begin
      if (en_masking) begin
        act_digest[i] = act_share0[i] ^ act_share1[i];
      end else begin
        act_digest[i] = act_share0[i];
      end

      // Compare the values
      `DV_CHECK_EQ_FATAL(exp_digest[i], act_digest[i],
          $sformatf("Mismatch between exp_digest[%0d] and act_digest[%0d]", i, i))
    end

  endfunction

endclass
