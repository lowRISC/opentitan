// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_sideload_aes_vseq extends chip_sw_keymgr_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_sideload_aes_vseq)

  `uvm_object_new

  // Plaintext 16B block (transposed) matching input at the SW test: `0x00112233445566778899aabbccddeeff`
  // Refer to `hw/ip/aes/rtl/aes_cipher_core.sv` for mapping plaintext input to the AES core.
  localparam bit [3:0][3:0][7:0] PlainText = {
             32'hffbb7733,
             32'heeaa6622,
             32'hdd995511,
             32'hcc884400
  };


  virtual task check_op_in_owner_int_state(bit [keymgr_pkg::KeyWidth-1:0] unmasked_key);

    bit [3:0][3:0][7:0] ciphertext;
    bit [3:0][3:0][7:0] ciphertext_transposed;
    bit [7:0] digest [16];
    bit [7:0] digest_rev [16];
    bit [keymgr_pkg::KeyWidth-1:0] sideload_aes_key;
    bit [keymgr_pkg::KeyWidth-1:0] sideload_aes_key_rev;

    // Only need to fetch the AES sideload key from keymgr and test it with AES and not check key generation.
    check_aes_sideload(unmasked_key, sideload_aes_key);

    // Compute AES block encryption (C model) with above unmasked key.
    aes_model_dpi_pkg::c_dpi_aes_crypt_block(1'b0, 1'b0, 6'b00_0001, 128'h0, 3'b100,
                           sideload_aes_key,
                           PlainText,
                           ciphertext);

    // Transpose, unpack and reverse byte order of ciphertext to match digest from AES HW core.
    ciphertext_transposed = aes_pkg::aes_transpose(ciphertext);
    {>>{digest}} = ciphertext_transposed;
    {<< byte {digest_rev}} = digest;

    // Transfer the expected AES digest to the C test via the backdoor SW symbol.
    sw_symbol_backdoor_overwrite("kAESDigest", digest_rev);

    // Reverse byte order of key to match the AES NIST.FIPS.197 standard.
    {<< byte {sideload_aes_key_rev}} = sideload_aes_key;

    `uvm_info(`gfn, $sformatf("AES Plaintext (C model): 0x%0h", PlainText), UVM_LOW)
    `uvm_info(`gfn, $sformatf("AES Ciphertext (C model): 0x%0h", ciphertext_transposed), UVM_LOW)
    `uvm_info(`gfn, $sformatf("AES Sideload Key0x%0h", sideload_aes_key_rev), UVM_LOW)

  endtask

endclass : chip_sw_keymgr_sideload_aes_vseq
