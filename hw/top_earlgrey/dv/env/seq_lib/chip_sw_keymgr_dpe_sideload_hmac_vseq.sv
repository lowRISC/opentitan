// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_dpe_sideload_hmac_vseq extends chip_sw_keymgr_dpe_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_sideload_hmac_vseq)

  `uvm_object_new

  // The following variables match their SW side equivalents
  localparam string Message = {"Every one suspects himself of at least one of ",
                               "the cardinal virtues, and this is mine: I am ",
                               "one of the few honest people that I have ever ",
                               "known"};
  localparam int DigestWords = 8;
  localparam int KeyWords = keymgr_dpe_pkg::WideHwKeyWidth / 32;

  virtual task run_test_sequence(key_shares_t creator_key);
    wide_key_t       sideload_hmac_key;
    bit [31:0]       key_words[KeyWords];
    string           msg;
    bit [7:0]        msg_arr[];
    bit [31:0]       exp_digest[DigestWords];
    bit [7:0]        digest_arr[DigestWords * 4];

    // Wait until the sideloaded key is generated
    cfg.sw_logger_vif.wait_for_log_message({"KeymgrDpe generated ",
                                            "HW output for HMAC from the CreatorRootKey"});

    // Check if the generated key matches the expected key
    check_generated_output(.key_shares(creator_key),
                           .dest(keymgr_dpe_pkg::Hmac),
                           .version(kVersionVersionedKey),
                           .salt(kSaltVersionedKey));

    // Fetch the generated key via backdoor from the HW!
    sideload_hmac_key = get_unmasked_wide_key(get_wide_output(keymgr_dpe_pkg::Hmac));

    // HMAC uses the sideloaded key as the most significant bits of its key, i.e., the first key
    // byte is `sideload_hmac_key[511:504]`.
    foreach (key_words[i]) begin
      key_words[i] = sideload_hmac_key[(keymgr_dpe_pkg::WideHwKeyWidth - 1) - 32 * i -: 32];
    end

    // Copy into a variable first, as string methods cannot be applied to class parameters.
    msg = Message;
    msg_arr = new[msg.len()];
    foreach (msg_arr[i]) msg_arr[i] = msg[i];

    cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key_words, msg_arr, exp_digest);

    // The DPI model returns the digest bytes packed in little-endian words. SW reads the digest
    // with `dif_hmac_finish()` and `kDifHmacEndiannessLittle`, i.e., word `i` of the SW digest is
    // `DIGEST_<7-i>`, which holds digest word `7-i` in big-endian byte order.
    for (int i = 0; i < DigestWords; i++) begin
      bit [31:0] sw_word = {<<8{exp_digest[DigestWords - 1 - i]}};
      for (int b = 0; b < 4; b++) digest_arr[4 * i + b] = sw_word[8 * b +: 8];
    end

    sw_symbol_backdoor_overwrite("sideload_digest_result", digest_arr);
  endtask

endclass : chip_sw_keymgr_dpe_sideload_hmac_vseq
