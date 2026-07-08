// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_dpe_sideload_kmac_vseq extends chip_sw_keymgr_dpe_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_sideload_kmac_vseq)

  `uvm_object_new

  // The following variables match their SW side equivalents
  localparam int MessageBytes = 4;
  localparam bit [7:0] MsgArr[MessageBytes] = {8'h00, 8'h01, 8'h02, 8'h03};
  localparam string CustomStr = "";
  localparam int DigestBytes = 32;
  localparam int KeyBytes = keymgr_pkg::KeyWidth / 8;

  virtual task run_test_sequence(key_shares_t creator_key);
    bit [keymgr_pkg::KeyWidth-1:0] sideload_kmac_key;
    bit [7:0] sideload_key_arr[KeyBytes];
    bit [7:0] digest_arr[DigestBytes];

    // Wait until the sideloaded key is generated
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated HW output for Kmac from the CreatorRootKey")

    // Check if the generated key matches the expected key
    check_generated_output(.key_shares(creator_key),
                           .dest(keymgr_pkg::Kmac),
                           .version(kVersionVersionedKey),
                           .salt(kSaltVersionedKey));

    // Fetch the generated key via backdoor from the HW!
    sideload_kmac_key = get_unmasked_key(get_output(keymgr_pkg::Kmac));
    {<< byte {sideload_key_arr}} = sideload_kmac_key;

    c_dpi_kmac128(MsgArr, MessageBytes,
                  sideload_key_arr, KeyBytes,
                  CustomStr,
                  DigestBytes, digest_arr);

    sw_symbol_backdoor_overwrite("sideload_digest_result", digest_arr);
  endtask

endclass : chip_sw_keymgr_dpe_sideload_kmac_vseq
