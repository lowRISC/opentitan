// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_dpe_sideload_aes_vseq extends chip_sw_keymgr_dpe_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_sideload_aes_vseq)

  `uvm_object_new

  // Plaintext 16B block (transposed) matching input at the SW test: `0x00112233445566778899aabbccddeeff`
  // Refer to `hw/ip/aes/rtl/aes_cipher_core.sv` for mapping plaintext input to the AES core.
  localparam bit [3:0][3:0][7:0] PlainText = {
             32'hffbb7733,
             32'heeaa6622,
             32'hdd995511,
             32'hcc884400
  };


  virtual task run_test_sequence(key_shares_t creator_key);

    bit [3:0][3:0][7:0] ciphertext;
    bit [3:0][3:0][7:0] ciphertext_transposed;
    bit [7:0] digest [16];
    bit [7:0] digest_rev [16];
    bit [keymgr_pkg::KeyWidth-1:0] sideload_aes_key;
    bit [keymgr_pkg::KeyWidth-1:0] sideload_aes_key_rev;

    // Wait until the sideloaded key is generated
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated HW output for Aes from the CreatorRootKey")

    // Check if the generated key matches the expected key
    check_generated_output(.key_shares(creator_key),
                           .dest(keymgr_pkg::Aes),
                           .version(kVersionVersionedKey),
                           .salt(kSaltVersionedKey));

    // Fetch the generated key via backdoor from the HW!
    sideload_aes_key = get_unmasked_key(get_output(keymgr_pkg::Aes));

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
    `uvm_info(`gfn, $sformatf("AES Sideload Key: 0x%0h", sideload_aes_key_rev), UVM_LOW)

  endtask

endclass : chip_sw_keymgr_dpe_sideload_aes_vseq
