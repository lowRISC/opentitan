// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_seq_item extends uvm_sequence_item;
  `uvm_object_utils(keymgr_dpe_seq_item)

  // Sideload keys output by keymgr_dpe.
  hw_key_req_t      m_aes_key;
  hw_key_req_t      m_kmac_key;
  wide_hw_key_req_t m_hmac_key;
  wide_hw_key_req_t m_otbn_key;

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
  extern function void print_narrow_hw_keys(hw_key_req_t key, string prefix, uvm_printer printer);
  extern function void print_wide_hw_keys(wide_hw_key_req_t key,
                                          string            prefix,
                                          uvm_printer       printer);
  extern function void print_lc_tx(lc_tx_t lc_tx, uvm_printer printer);
  extern function void print_root_key(keymgr_dpe_creator_root_key_t key,
                                      string                        prefix,
                                      uvm_printer                   printer);
  extern function void print_seed(keymgr_dpe_creator_seed_t seed,
                                  string                    prefix,
                                  uvm_printer               printer);
  extern function void print_field_entropy(keymgr_dpe_field_entropy_t field_entropy,
                                           uvm_printer                printer);
  extern function void print_rom_digest(keymgr_data_t [NUM_ROM_DIGESTS-1:0] rom_digest,
                                        uvm_printer                         printer);
  extern virtual function void do_print(uvm_printer printer);
endclass

function keymgr_dpe_seq_item::new(string name="");
  super.new(name);
endfunction

function void keymgr_dpe_seq_item::print_narrow_hw_keys(hw_key_req_t key,
                                                        string       prefix,
                                                        uvm_printer  printer);
  printer.print_field($sformatf("%0s_key.valid", prefix), key.valid, 1, UVM_BIN);
  printer.print_field($sformatf("%0s_key.key[0]", prefix), key.key[0], $bits(key.key[0]), UVM_HEX);
  printer.print_field($sformatf("%0s_key.key[1]", prefix), key.key[1], $bits(key.key[1]), UVM_HEX);
endfunction

function void keymgr_dpe_seq_item::print_wide_hw_keys(wide_hw_key_req_t key,
                                                      string            prefix,
                                                      uvm_printer       printer);
  printer.print_field($sformatf("%0s_key.valid", prefix), key.valid, 1, UVM_BIN);
  printer.print_field($sformatf("%0s_key.key[0]", prefix), key.key[0], $bits(key.key[0]), UVM_HEX);
  printer.print_field($sformatf("%0s_key.key[1]", prefix), key.key[1], $bits(key.key[1]), UVM_HEX);
endfunction

function void keymgr_dpe_seq_item::print_lc_tx(lc_tx_t lc_tx, uvm_printer printer);
  printer.print_string("m_lc_keymgr_en", $sformatf("%0s (0x%0h)", lc_tx.name(), lc_tx));
endfunction

function void keymgr_dpe_seq_item::print_root_key(keymgr_dpe_creator_root_key_t key,
                                                  string prefix,
                                                  uvm_printer printer);

  printer.print_field($sformatf("%0s_key.share0", prefix), key.share0, $bits(key.share0), UVM_HEX);
  printer.print_field($sformatf("%0s_key.share0_valid", prefix), key.share0_valid, 1, UVM_BIN);
  printer.print_field($sformatf("%0s_key.share1", prefix), key.share1, $bits(key.share1), UVM_HEX);
  printer.print_field($sformatf("%0s_key.share1_valid", prefix), key.share1_valid, 1, UVM_BIN);
endfunction

function void keymgr_dpe_seq_item::print_seed(keymgr_dpe_creator_seed_t seed,
                                              string prefix,
                                              uvm_printer printer);

  printer.print_field($sformatf("%0s_seed.seed", prefix), seed.seed, $bits(seed.seed), UVM_HEX);
  printer.print_field($sformatf("%0s_seed.seed_valid", prefix), seed.seed_valid, 1, UVM_BIN);
endfunction

function void keymgr_dpe_seq_item::print_field_entropy(keymgr_dpe_field_entropy_t field_entropy,
                                                       uvm_printer printer);
  printer.print_field("field_entropy.secret",
                      field_entropy.secret,
                      $bits(field_entropy.secret),
                      UVM_HEX);
  printer.print_field("field_entropy.secret_valid",
                      field_entropy.secret_valid,
                      1,
                      UVM_BIN);
endfunction

function void keymgr_dpe_seq_item::print_rom_digest(keymgr_data_t [NUM_ROM_DIGESTS-1:0] rom_digest,
                                                    uvm_printer printer);
  foreach(rom_digest[i]) begin
    printer.print_field($sformatf("rom_digest[%0d].data", i),
                        rom_digest[i].data,
                        $bits(rom_digest[i].data),
                        UVM_HEX);
    printer.print_field($sformatf("rom_digest[%0d].valid", i), rom_digest[i].valid, 1, UVM_BIN);
  end
endfunction

function void keymgr_dpe_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);

  print_narrow_hw_keys(m_aes_key, "aes", printer);
  print_narrow_hw_keys(m_kmac_key, "kmac", printer);
  print_wide_hw_keys(m_hmac_key, "hmac", printer);
  print_wide_hw_keys(m_otbn_key, "otbn", printer);
  print_lc_tx(m_lc_keymgr_en, printer);
  printer.print_field("m_lc_keymgr_div", m_lc_keymgr_div, $bits(m_lc_keymgr_div), UVM_HEX);
  print_root_key(m_root_key, "root", printer);
  print_root_key(m_secondary_root_key, "secondary_root", printer);
  print_seed(m_creator_seed, "creator", printer);
  print_seed(m_owner_seed, "owner", printer);
  printer.print_field("m_device_id", m_device_id, $bits(m_device_id), UVM_HEX);
  print_field_entropy(m_field_entropy, printer);
  print_rom_digest(m_rom_digest, printer);
endfunction
