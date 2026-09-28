// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence interacts with the test sw/device/tests/keymgr_dpe_otbn_hkdf_smoketest.c.
//
// - The base sequence checks the UDS and the CreatorRootKey derivation.
// - The SW selects OTBN as KDF engine and advances the CreatorRootKey context in place.
// - This sequence checks that exactly one slot holds the derived key at boot stage 2 and that the
//   derived key differs from the CreatorRootKey.
class chip_sw_keymgr_dpe_otbn_hkdf_vseq extends chip_sw_keymgr_dpe_key_derivation_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_otbn_hkdf_vseq)

  `uvm_object_new

  virtual task run_test_sequence(key_shares_t creator_key);
    key_shares_t key;
    int key_slot_idx;

    // Wait for keymgr_dpe to derive a DPE context with OTBN as KDF engine.
    cfg.sw_logger_vif.wait_for_log_message("KeymgrDpe derived DPE context with the OTBN (HKDF)");

    // At this point, exactly one key slot should contain a key. This key must be the child of the
    // CreatorRootKey, i.e., it has advanced to boot stage 2. Verify that this holds.
    begin
      bit key_found = 1'b0;
      key_slot_idx = 0;
      for (int i = 0; i < num_hw_slots; i++) begin
        keymgr_dpe_pkg::keymgr_dpe_slot_t slot = get_key_slot(i);
        if (slot.valid) begin
          `DV_CHECK_EQ(key_found, 1'b0, "Expecting only one key")
          `DV_CHECK_EQ(slot.boot_stage, keymgr_dpe_pkg::BootStageOwnerInt,
                       "Expecting the derived key to be in boot stage 2")
          key_found = 1'b1;
          key = slot.key;
          key_slot_idx = i;
        end
      end
      `DV_CHECK_EQ(key_found, 1'b1, "Expecting one valid key slot")
    end

    // The derived key must differ from its parent.
    `DV_CHECK_NE(get_unmasked_key(key), get_unmasked_key(creator_key),
                 "Expecting the derived key to differ from the CreatorRootKey")


    // The OTBN app returns a fixed response, so the derived key is known exactly.
    begin
      bit [7:0] resp_s0_bytes[], resp_s1_bytes[];
      bit [kmac_pkg::AppDigestW-1:0] resp_s0, resp_s1;
      key_t exp_key;

      resp_s0_bytes = new[kmac_pkg::AppDigestW / 8];
      resp_s1_bytes = new[kmac_pkg::AppDigestW / 8];
      sw_symbol_backdoor_read("kOtbnResponseS0", resp_s0_bytes);
      sw_symbol_backdoor_read("kOtbnResponseS1", resp_s1_bytes);
      // Byte 0 is the least significant byte (SW writes DMEM little-endian).
      resp_s0 = {<< byte {resp_s0_bytes}};
      resp_s1 = {<< byte {resp_s1_bytes}};

      // Only the lower `InternalKeyWidth` bits of the kmac digest are used as key
      `uvm_info(`gfn, $sformatf("Derived share0 (slot %d) vs fixed response\n%h\n%h", key_slot_idx,
          key[0], resp_s0[keymgr_dpe_pkg::InternalKeyWidth-1:0]), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("Derived share1 (slot %d) vs fixed response\n%h\n%h", key_slot_idx,
          key[1], resp_s1[keymgr_dpe_pkg::InternalKeyWidth-1:0]), UVM_MEDIUM)

      // Compare each share with the known answer
      `DV_CHECK_EQ(resp_s0[keymgr_dpe_pkg::InternalKeyWidth-1:0], key[0],
                   "Derived share 0 does not match the fixed OTBN response")
      `DV_CHECK_EQ(resp_s1[keymgr_dpe_pkg::InternalKeyWidth-1:0], key[1],
                   "Derived share 1 does not match the fixed OTBN response")
    end

    // Print the generated key
    `uvm_info(`gfn, $sformatf("Derived key in slot %0d:\n%s", key_slot_idx,
        key_shares_str(key)), UVM_LOW)
  endtask

endclass : chip_sw_keymgr_dpe_otbn_hkdf_vseq
