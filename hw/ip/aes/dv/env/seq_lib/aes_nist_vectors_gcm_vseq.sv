// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test to encrypt/decrypt NIST test vectors.
// The output of the DUT is compared both against the output of the golden model
// and against the known test vector output.

import nist_vectors_gcm_pkg::*;
class aes_nist_vectors_gcm_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_nist_vectors_gcm_vseq)

  `uvm_object_new

  bit [3:0] [31:0]      len_ctx_aad;
  bit [3:0] [31:0]      tag;
  bit [3:0] [31:0]      aad[4];
  bit [3:0] [31:0]      plain_text[4];
  bit [7:0] [31:0]      init_key[2]      = '{256'h0, 256'h0};
  bit [3:0] [31:0]      iv;
  bit [3:0] [31:0]      cipher_text[4];
  bit [3:0] [31:0]      decrypted_text[4];
  bit                   do_b2b = 0;
  int                   num_vec = 0;

  aes_nist_vectors_gcm  nist_obj = new;
  nist_vector_gcm_t     nist_vectors[];

  virtual      aes_cov_if   cov_if;           // handle to aes coverage interface

  task body();

    if (!uvm_config_db#(virtual aes_cov_if)::get(null, "*.env" , "aes_cov_if", cov_if)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO COVER IF"))
    end

    `uvm_info(`gfn, $sformatf("STARTING AES NIST VECTOR GCM SEQUENCE"), UVM_LOW)
    num_vec = nist_obj.get_num_vectors_gcm();
    nist_vectors = new[num_vec];
    nist_vectors = nist_obj.vector_q;

    `uvm_info(`gfn, $sformatf("size of array %d", nist_vectors.size()), UVM_LOW)

    `DV_CHECK_RANDOMIZE_FATAL(this)

    foreach (nist_vectors[i]) begin
      /*****************************************************************************/
      /** AES-GCM-128 Encryption                                                  **/
      /*****************************************************************************/
      int num_aad_blocks = nist_vectors[i].num_aad_blocks;
      int num_ptx_blocks = nist_vectors[i].num_plain_text_blocks;
      int last_plain_text_block_size = nist_vectors[i].last_plain_text_block_size;
      int last_aad_block_size = nist_vectors[i].last_aad_block_size;
      int aad_block_zero = num_aad_blocks == 0 ? 1 : 0;
      int ptx_block_zero = num_ptx_blocks == 0 ? 1 : 0;
      // Wait for dut idle.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      `uvm_info(`gfn, $sformatf("%s", vectorgcm2string(nist_vectors[i]) ), UVM_LOW)
      `uvm_info(`gfn, $sformatf(" \n\t ---|setting operation to encrypt"), UVM_MEDIUM)

      // Config AES core.
      ral.ctrl_shadowed.operation.set(AES_ENC);
      ral.ctrl_shadowed.key_len.set(nist_vectors[i].key_len);
      ral.ctrl_shadowed.mode.set(nist_vectors[i].mode);
      ral.ctrl_shadowed.prng_reseed_rate.set(PER_8K);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));

      // Put AES-GCM into init phase.
      cov_if.cg_ctrl_gcm_reg_sample(GCM_INIT);
      set_gcm_phase(GCM_INIT, 16, 1);

      // Write key registers.
      // Transpose key to match NIST format (<little endian).
      init_key = '{ {<<8{nist_vectors[i].key}},  256'h0 };
      write_key(init_key, do_b2b);

      // Write IV registers.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Transpose IV to match NIST format (little endian).
      iv = {<<8{nist_vectors[i].iv}};
      write_iv(iv, do_b2b);

      // Write AAD.
      if (num_aad_blocks > 0) begin
        // Put AES-GCM into AAD phase.
        int valid_bytes = 16;
        if (num_aad_blocks == 1) begin
          valid_bytes = last_aad_block_size;
        end
        `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING AAD"), UVM_MEDIUM)
        cov_if.cg_ctrl_gcm_reg_sample(GCM_AAD);
        set_gcm_phase(GCM_AAD, valid_bytes, 1);

        // Write all except the last AAD block into the data registers.
        for (int n = 0; n < num_aad_blocks - 1; n++) begin
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          aad[n] = {<<8{nist_vectors[i].aad[n]}};
          add_data(aad[n], do_b2b);
        end

        // For the last block, check if the block size is smaller than 16 bytes.
        // Then we need to again put AES-GCM into the AAD phase with the block size.
        if (num_aad_blocks != 1 && last_aad_block_size != 16) begin
          cov_if.cg_ctrl_gcm_reg_sample(GCM_AAD);
          set_gcm_phase(GCM_AAD, last_aad_block_size, 1);
        end
        // Write last AAD block to AES.
        csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
        aad[num_aad_blocks - 1] = {<<8{nist_vectors[i].aad[num_aad_blocks - 1]}};
        add_data(aad[num_aad_blocks - 1], do_b2b);
      end

      // Write PTX.
      if (num_ptx_blocks > 0) begin
        // Put AES-GCM into TEXT phase.
        int valid_bytes = 16;
        if (num_ptx_blocks == 1) begin
          valid_bytes = last_plain_text_block_size;
        end
        `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING PLAIN TEXT"), UVM_MEDIUM)
        cov_if.cg_ctrl_gcm_reg_sample(GCM_TEXT);
        set_gcm_phase(GCM_TEXT, valid_bytes, 1);

        // Write all except the last PTX block into the data registers.
        for (int n = 0; n < num_ptx_blocks - 1; n++) begin
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          plain_text[n] = {<<8{nist_vectors[i].plain_text[n]}};
          add_data(plain_text[n], do_b2b);
          // Read ciphertext.
          csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
          read_data(cipher_text[n], do_b2b);
        end

        // For the last block, check if the block size is smaller than 16 bytes.
        // Then we need to again put AES-GCM into the TEXT phase with the block size.
        if (num_ptx_blocks != 1 && last_plain_text_block_size != 16) begin
          cov_if.cg_ctrl_gcm_reg_sample(GCM_TEXT);
          set_gcm_phase(GCM_TEXT, last_plain_text_block_size, 1);
        end
        // Write last PTX block to AES.
        csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
        plain_text[num_ptx_blocks - 1] =
          {<<8{nist_vectors[i].plain_text[num_ptx_blocks - 1]}};
        add_data(plain_text[num_ptx_blocks - 1], do_b2b);
        // Read ciphertext.
        csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
        read_data(cipher_text[num_ptx_blocks - 1], do_b2b);

        // Compare the received cipher text to the NIST test vector.
        for (int n = 0; n < num_ptx_blocks - 1; n++) begin
          cipher_text[n] =  {<<8{cipher_text[n]}};
          if (cipher_text[n] != nist_vectors[i].cipher_text[n]) begin
            `uvm_error(`gfn,
              $sformatf("Result does not match for vector[%d][%d], \n nist: %0h \n output: %0h",
                        i,n, nist_vectors[i].cipher_text[n], cipher_text[n]))
          end
        end
      end

      `uvm_info(`gfn, $sformatf(" \n\t ---| READ TAG"), UVM_MEDIUM)
      // Put AES-GCM into TAG mode and write len(ad) || len(pt).
      cov_if.cg_ctrl_gcm_reg_sample(GCM_TAG);
      set_gcm_phase(GCM_TAG, 16, 1);
      csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
      len_ctx_aad = {<<8{nist_vectors[i].len_ctx_aad}};
      add_data(len_ctx_aad, do_b2b);
      // Read out the tag.
      csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
      read_data(tag, do_b2b);
      tag = {<<8{tag}};
      if (nist_vectors[i].tag != tag) begin
        `uvm_fatal(`gfn,
          $sformatf("Tag does not match for vector %d, \n nist: %0h \n output: %0h",
                    i, nist_vectors[i].tag, tag));
      end

      // After checking the output, sample the current message for the coverage.
      cov_if.cg_gcm_len_sample(num_aad_blocks, last_aad_block_size, aad_block_zero,
                               num_ptx_blocks, last_plain_text_block_size, ptx_block_zero,
                               AES_ENC);

      /*****************************************************************************/
      /** AES-GCM-128 Decryption                                                  **/
      /*****************************************************************************/
      // Wait for dut idle.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      `uvm_info(`gfn, $sformatf(" \n\t ---|setting operation to decrypt"), UVM_MEDIUM)

      // Config AES core.
      ral.ctrl_shadowed.operation.set(AES_DEC);
      ral.ctrl_shadowed.key_len.set(nist_vectors[i].key_len);
      ral.ctrl_shadowed.mode.set(nist_vectors[i].mode);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));

      // Put AES-GCM into init phase.
      cov_if.cg_ctrl_gcm_reg_sample(GCM_INIT);
      set_gcm_phase(GCM_INIT, 16, 1);

      // Write key registers.
      // Transpose key to match NIST format (<little endian).
      init_key = '{ {<<8{nist_vectors[i].key}},  256'h0 };
      write_key(init_key, do_b2b);

      // Write IV registers.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Transpose IV to match NIST format (little endian).
      iv = {<<8{nist_vectors[i].iv}};
      write_iv(iv, do_b2b);

      // Write AAD.
      if (num_aad_blocks > 0) begin
        // Put AES-GCM into AAD phase.
        int valid_bytes = 16;
        if (num_aad_blocks == 1) begin
          valid_bytes = last_aad_block_size;
        end
        `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING AAD"), UVM_MEDIUM)
        cov_if.cg_ctrl_gcm_reg_sample(GCM_AAD);
        set_gcm_phase(GCM_AAD, valid_bytes, 1);

        // Write all except the last AAD block into the data registers.
        for (int n = 0; n < num_aad_blocks - 1; n++) begin
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          aad[n] = {<<8{nist_vectors[i].aad[n]}};
          add_data(aad[n], do_b2b);
        end

        // For the last block, check if the block size is smaller than 16 bytes.
        // Then we need to again put AES-GCM into the AAD phase with the block size.
        if (num_aad_blocks != 1 && last_aad_block_size != 16) begin
          cov_if.cg_ctrl_gcm_reg_sample(GCM_AAD);
          set_gcm_phase(GCM_AAD, last_aad_block_size, 1);
        end
        // Write last AAD block to AES.
        csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
        aad[num_aad_blocks - 1] = {<<8{nist_vectors[i].aad[num_aad_blocks - 1]}};
        add_data(aad[num_aad_blocks - 1], do_b2b);
      end

      // Write CTX.
      if (num_ptx_blocks > 0) begin
        // Put AES-GCM into TEXT phase.
        int valid_bytes = 16;
        if (num_ptx_blocks == 1) begin
          valid_bytes = last_plain_text_block_size;
        end
        `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING CIPHER TEXT"), UVM_MEDIUM)
        cov_if.cg_ctrl_gcm_reg_sample(GCM_TEXT);
        set_gcm_phase(GCM_TEXT, valid_bytes, 1);

        // Write all except the last CTX block into the data registers.
        for (int n = 0; n < num_ptx_blocks - 1; n++) begin
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          cipher_text[n] = {<<8{nist_vectors[i].cipher_text[n]}};
          add_data(cipher_text[n], do_b2b);
          // Read ciphertext.
          csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
          read_data(plain_text[n], do_b2b);
        end

        // For the last block, check if the block size is smaller than 16 bytes.
        // Then we need to again put AES-GCM into the TEXT phase with the block size.
        if (num_ptx_blocks != 1 && last_plain_text_block_size != 16) begin
          cov_if.cg_ctrl_gcm_reg_sample(GCM_TEXT);
          set_gcm_phase(GCM_TEXT, last_plain_text_block_size, 1);
        end
        // Write last CTX block to AES.
        csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
        cipher_text[num_ptx_blocks - 1] =
          {<<8{nist_vectors[i].cipher_text[num_ptx_blocks - 1]}};
        add_data(cipher_text[num_ptx_blocks - 1], do_b2b);
        // Read ciphertext.
        csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
        read_data(plain_text[num_ptx_blocks - 1], do_b2b);

        // Compare the received plain text to the NIST test vector.
        for (int n = 0; n < num_ptx_blocks - 1; n++) begin
          plain_text[n] =  {<<8{plain_text[n]}};
          if (plain_text[n] != nist_vectors[i].plain_text[n]) begin
            `uvm_error(`gfn,
              $sformatf("Result does not match for vector[%d][%d], \n nist: %0h \n output: %0h",
                        i,n, nist_vectors[i].plain_text[n], plain_text[n]))
          end
        end
      end

      `uvm_info(`gfn, $sformatf(" \n\t ---| READ TAG"), UVM_MEDIUM)
      // Put AES-GCM into TAG mode and write len(ad) || len(pt).
      cov_if.cg_ctrl_gcm_reg_sample(GCM_TAG);
      set_gcm_phase(GCM_TAG, 16, 1);
      csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
      len_ctx_aad = {<<8{nist_vectors[i].len_ctx_aad}};
      add_data(len_ctx_aad, do_b2b);
      // Read out the tag.
      csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
      read_data(tag, do_b2b);
      tag = {<<8{tag}};
      if (nist_vectors[i].tag != tag) begin
        `uvm_fatal(`gfn,
          $sformatf("Tag does not match for vector %d, \n nist: %0h \n output: %0h",
                    i, nist_vectors[i].tag, tag));
      end

      // After checking the output, sample the current message for the coverage.
      cov_if.cg_gcm_len_sample(num_aad_blocks, last_aad_block_size, aad_block_zero,
                               num_ptx_blocks, last_plain_text_block_size, ptx_block_zero,
                               AES_DEC);

    end
    `uvm_info(`gfn, $sformatf(" \n\t ---| YAY TEST PASSED |--- \n \t "), UVM_NONE)
  endtask : body
endclass : aes_nist_vectors_gcm_vseq
