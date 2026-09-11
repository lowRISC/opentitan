// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_dpe_sideload_hmac_vseq extends chip_sw_keymgr_dpe_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_sideload_hmac_vseq)

  `uvm_object_new


  virtual task run_test_sequence(key_shares_t creator_key);
    wide_key_t hmac_key;

    // Wait until the sideloaded key is generated
    `DV_WAIT(cfg.sw_logger_vif.printed_log ==
        "KeymgrDpe generated HW output for HMAC from the CreatorRootKey")

    // Check if the generated key matches the expected key
    check_generated_output(.key_shares(creator_key),
                           .dest(keymgr_dpe_pkg::Hmac),
                           .version(kVersionVersionedKey),
                           .salt(kSaltVersionedKey));

    // Fetch the generated key via backdoor from the HW!
    hmac_key = get_unmasked_wide_key(get_wide_output(keymgr_dpe_pkg::Hmac));

    // TODO(#31206): Implement this hmac vseq
    `uvm_info(`gfn, "HMAC vseq not implemented yet.", UVM_LOW)
  endtask

endclass : chip_sw_keymgr_dpe_sideload_hmac_vseq
