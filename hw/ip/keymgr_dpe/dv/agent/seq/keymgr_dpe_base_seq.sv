// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence is used to initialize the HW inputs for keymgr_dpe.
class keymgr_dpe_base_seq extends dv_base_seq #(.REQ(keymgr_dpe_seq_item),
                                                .SEQUENCER_T(keymgr_dpe_sequencer));

  `uvm_object_utils(keymgr_dpe_base_seq)

  // LC interface to enable / disable keymgr_dpe.
  rand lc_tx_t         m_lc_keymgr_en;
  rand lc_keymgr_div_t m_lc_keymgr_div;

  // Root keys.
  rand keymgr_dpe_creator_root_key_t m_root_key;
  rand keymgr_dpe_creator_root_key_t m_secondary_root_key;

  // Utilized as HW bindings in the KDF message argument (child_key = KDF(parent_key, message)).
  rand keymgr_dpe_creator_seed_t           m_creator_seed;
  rand keymgr_dpe_owner_seed_t             m_owner_seed;
  rand keymgr_dpe_device_id_t              m_device_id;
  rand keymgr_dpe_field_entropy_t          m_field_entropy;
  rand keymgr_data_t [NUM_ROM_DIGESTS-1:0] m_rom_digest;

  extern function new(string name="");
  extern virtual task body();

  extern constraint m_valid_lc_keymgr_en_c;
  extern constraint m_valid_lc_keymgr_div_c;
  extern constraint m_valid_root_key_c;
  extern constraint m_valid_secondary_root_key_c;
  extern constraint m_valid_creator_seed_c;
  extern constraint m_valid_owner_seed_c;
  extern constraint m_valid_device_id_c;
  extern constraint m_valid_field_entropy_c;
  extern constraint m_valid_rom_digest_c;
endclass

function keymgr_dpe_base_seq::new(string name="");
  super.new(name);
endfunction

task keymgr_dpe_base_seq::body();
  REQ item = REQ::type_id::create("item");

  start_item(item);

  if (!item.randomize() with {
      item.m_lc_keymgr_en       == local::m_lc_keymgr_en;
      item.m_lc_keymgr_div      == local::m_lc_keymgr_div;
      item.m_root_key           == local::m_root_key;
      item.m_secondary_root_key == local::m_secondary_root_key;
      item.m_creator_seed       == local::m_creator_seed;
      item.m_owner_seed         == local::m_owner_seed;
      item.m_device_id          == local::m_device_id;
      item.m_field_entropy      == local::m_field_entropy;
      item.m_rom_digest         == local::m_rom_digest;})
    `uvm_fatal(`gfn, "Failed to randomize item!")

  // Assert the valid bits of the fields.
  item.m_root_key.share0_valid           = 1'b1;
  item.m_root_key.share1_valid           = 1'b1;
  item.m_secondary_root_key.share0_valid = 1'b1;
  item.m_secondary_root_key.share1_valid = 1'b1;
  item.m_creator_seed.seed_valid         = 1'b1;
  item.m_owner_seed.seed_valid           = 1'b1;
  item.m_field_entropy.secret_valid      = 1'b1;

  foreach(item.m_rom_digest[i])
    item.m_rom_digest[i].valid = 1'b1;

  finish_item(item);
endtask

constraint keymgr_dpe_base_seq::m_valid_lc_keymgr_en_c {
  m_lc_keymgr_en == lc_ctrl_pkg::On;
}

constraint keymgr_dpe_base_seq::m_valid_lc_keymgr_div_c {
  m_lc_keymgr_div != '0;
  m_lc_keymgr_div != '1;
}

constraint keymgr_dpe_base_seq::m_valid_root_key_c {
  m_root_key != '0;
  m_root_key != '1;
}

constraint keymgr_dpe_base_seq::m_valid_secondary_root_key_c {
  m_secondary_root_key != '0;
  m_secondary_root_key != '1;
}

constraint keymgr_dpe_base_seq::m_valid_creator_seed_c {
  m_creator_seed != '0;
  m_creator_seed != '1;
}

constraint keymgr_dpe_base_seq::m_valid_owner_seed_c {
  m_owner_seed != '0;
  m_owner_seed != '1;
}

constraint keymgr_dpe_base_seq::m_valid_device_id_c {
  m_device_id != '0;
  m_device_id != '1;
}

constraint keymgr_dpe_base_seq::m_valid_field_entropy_c {
  m_field_entropy != '0;
  m_field_entropy != '1;
}

constraint keymgr_dpe_base_seq::m_valid_rom_digest_c {
  foreach(m_rom_digest[i]) {
    m_rom_digest[i] != '0;
    m_rom_digest[i] != '1;
  }
}
