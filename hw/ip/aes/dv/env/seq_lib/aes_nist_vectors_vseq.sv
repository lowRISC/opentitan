// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test to encrypt/decrypt NIST test vectors.
// The output of the DUT is compared both against the output of the golden model
// and against the known test vector output.

import nist_vectors_pkg::*;
class aes_nist_vectors_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_nist_vectors_vseq)

  `uvm_object_new

  bit [3:0] [31:0]      plain_text[4];
  bit [7:0] [31:0]      init_key[2]      = '{256'h0, 256'h0};
  bit [3:0] [31:0]      iv;
  bit [3:0] [31:0]      cipher_text[4];
  bit [3:0] [31:0]      decrypted_text[4];
  bit                   do_b2b = 0;
  int                   num_vec = 0;

  aes_nist_vectors      nist_obj = new;
  nist_vector_t         nist_vectors[];


  task body();

    `uvm_info(`gfn, $sformatf("STARTING AES NIST VECTOR SEQUENCE"), UVM_LOW)
    num_vec = nist_obj.get_num_vectors();
    nist_vectors = new[num_vec];
    nist_vectors = nist_obj.vector_q;

    `uvm_info(`gfn, $sformatf("size of array %d", nist_vectors.size()), UVM_LOW)

    `DV_CHECK_RANDOMIZE_FATAL(this)

    foreach (nist_vectors[i]) begin
      // wait for dut idle
      csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
      `uvm_info(`gfn, $sformatf("%s", vector2string(nist_vectors[i]) ), UVM_LOW)
      `uvm_info(`gfn, $sformatf(" \n\t ---|setting operation to encrypt"), UVM_MEDIUM)

      // update CTRL reg //
      ral.ctrl_shadowed.operation.set(AES_ENC);
      ral.ctrl_shadowed.key_len.set(nist_vectors[i].key_len);
      ral.ctrl_shadowed.mode.set(nist_vectors[i].mode);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
      // transpose key To match NIST format ( little endian)
      init_key = '{ {<<8{nist_vectors[i].key}} ,  256'h0 };
      write_key(init_key, do_b2b);
      if (nist_vectors[i].mode != AES_ECB) begin
        csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
        iv = {<<8{nist_vectors[i].iv}};
        write_iv(iv, do_b2b);
      end

      `uvm_info(`gfn, $sformatf(" \n\t ---| ADDING PLAIN TEXT"), UVM_MEDIUM)

      foreach (nist_vectors[i].plain_text[n]) begin
        csr_spinwait(.ptr(ral.status.input_ready) , .exp_data(1'b1));
        // transpose input text
        plain_text[n] = {<<8{nist_vectors[i].plain_text[n]}};
        add_data(plain_text[n], do_b2b);

        // poll status register
        `uvm_info(`gfn, $sformatf("\n\t ---| Polling for data register %s",
                                  ral.status.convert2string()), UVM_DEBUG)

        csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));
        read_data(cipher_text[n], do_b2b);
      end

      foreach (nist_vectors[i].plain_text[n]) begin
        cipher_text[n] =  {<<8{cipher_text[n]}};
        `uvm_info(`gfn, $sformatf("calculated cipher %0h",cipher_text[n]), UVM_LOW)
        if (cipher_text[n] != nist_vectors[i].cipher_text[n]) begin
          `uvm_error(`gfn, $sformatf("Result does not match NIST for vector[%d][%d], \n nist: %0h \n output: %0h", i,n,
                                   nist_vectors[i].cipher_text[n], cipher_text[n]))
        end
      end

      ral.ctrl_shadowed.operation.set(AES_DEC);
      ral.ctrl_shadowed.key_len.set(nist_vectors[i].key_len);
      ral.ctrl_shadowed.mode.set(nist_vectors[i].mode);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));

      // transpose key To match NIST format ( little endian)
      init_key = '{ {<<8{nist_vectors[i].key}} ,  256'h0 };
      write_key(init_key, do_b2b);
      if (nist_vectors[i].mode != AES_ECB) begin
        csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
        iv = {<<8{nist_vectors[i].iv}};
        write_iv(iv, do_b2b);
      end

      foreach (nist_vectors[i].plain_text[n]) begin
        csr_spinwait(.ptr(ral.status.input_ready) , .exp_data(1'b1));
        // transpose input text
        cipher_text[n] =  {<<8{cipher_text[n]}};
        add_data(cipher_text[n], do_b2b);
        csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));
        read_data(decrypted_text[n], do_b2b);
      end
      foreach (nist_vectors[i].cipher_text[n]) begin
        decrypted_text[n] = {<<8{decrypted_text[n]}};
        if(nist_vectors[i].plain_text[n] != decrypted_text[n]) begin
          `uvm_fatal(`gfn, $sformatf("Decrypted Result does not match NIST for vector[%d][%d], \n nist: %0h \n output: %0h", i,n,
                                   nist_vectors[i].plain_text[n], decrypted_text[n]));
        end
      end
    end
    `uvm_info(`gfn, $sformatf(" \n\t ---| YAY TEST PASSED |--- \n \t "), UVM_NONE)
  endtask : body
endclass : aes_nist_vectors_vseq
