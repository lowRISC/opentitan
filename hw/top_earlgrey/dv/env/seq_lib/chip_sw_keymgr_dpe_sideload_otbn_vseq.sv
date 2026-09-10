// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_keymgr_dpe_sideload_otbn_vseq extends chip_sw_keymgr_dpe_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_sideload_otbn_vseq)

  `uvm_object_new


  virtual task run_test_sequence(key_shares_t creator_key);
    keymgr_pkg::otbn_key_req_t otbn_key;
    otbn_key_shares_t otbn_key_shares;

    // Wait until the sideloaded key is generated
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated HW output for OTBN from the CreatorRootKey")

    // Check if the generated key matches the expected key
    check_generated_output(.key_shares(creator_key),
                           .dest(keymgr_pkg::Otbn),
                           .version(kVersionVersionedKey),
                           .salt(kSaltVersionedKey));

    // Fetch the generated key via backdoor from the HW!
    otbn_key_shares = get_output_otbn();
    otbn_key = otbn_key_shares[1] ^ otbn_key_shares[0];

    // TODO(#30689): Implement this otbn vseq
    `uvm_info(`gfn, "OTBN vseq not implemented yet.", UVM_LOW)
  endtask

endclass : chip_sw_keymgr_dpe_sideload_otbn_vseq
