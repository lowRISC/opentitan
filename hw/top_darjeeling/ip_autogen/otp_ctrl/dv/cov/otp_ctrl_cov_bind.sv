// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds OTP_CTRL functional coverage interaface to the top level OTP_CTRL module.
//
`define PART_MUBI_COV(__part_name, __index)                                           \
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) ``__part_name``_read_lock_mubi_cov_if (  \
    .rst_ni (rst_ni),                                                                 \
    .mubi   (part_access[``__index``].read_lock)                                      \
  );                                                                                  \
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) ``__part_name``_write_lock_mubi_cov_if ( \
    .rst_ni (rst_ni),                                                                 \
    .mubi   (part_access[``__index``].write_lock)                                     \
  );

`define DAI_MUBI_COV(__part_name, __index)                                                \
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) dai_``__part_name``_read_lock_mubi_cov_if (  \
    .rst_ni (rst_ni),                                                                     \
    .mubi   (part_access_dai[``__index``].read_lock)                                      \
  );                                                                                      \
  bind otp_ctrl cip_mubi_cov_if #(.Width(8)) dai_``__part_name``_write_lock_mubi_cov_if ( \
    .rst_ni (rst_ni),                                                                     \
    .mubi   (part_access_dai[``__index``].write_lock)                                     \
  );

module otp_ctrl_cov_bind;
  import otp_ctrl_part_pkg::*;

  bind otp_ctrl otp_ctrl_cov_if u_otp_ctrl_cov_if (
    .pwr_otp_o        (pwr_otp_o),
    .lc_otp_program_i (lc_otp_program_i),
    .lc_escalate_en_i (lc_escalate_en_i),
    .sram_otp_key_i   (sram_otp_key_i),
    .otbn_otp_key_i   (otbn_otp_key_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_creator_seed_sw_rw_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_creator_seed_sw_rw_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_seed_hw_rd_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_seed_hw_rd_en_i)
  );

  bind otp_macro cip_lc_tx_cov_if u_lc_dft_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_dft_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_escalate_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_escalate_en_i)
  );

  bind otp_ctrl cip_lc_tx_cov_if u_lc_check_byp_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_check_byp_en_i)
  );

  // Mubi internal coverage for buffered and unbuffered partitions.
  `PART_MUBI_COV(vendor_test, otp_ctrl_part_pkg::VendorTestIdx)
  `PART_MUBI_COV(creator_sw_cfg, otp_ctrl_part_pkg::CreatorSwCfgIdx)
  `PART_MUBI_COV(owner_sw_cfg, otp_ctrl_part_pkg::OwnerSwCfgIdx)
  `PART_MUBI_COV(ownership_slot_state, otp_ctrl_part_pkg::OwnershipSlotStateIdx)
  `PART_MUBI_COV(rot_creator_auth, otp_ctrl_part_pkg::RotCreatorAuthIdx)
  `PART_MUBI_COV(rot_owner_auth_slot0, otp_ctrl_part_pkg::RotOwnerAuthSlot0Idx)
  `PART_MUBI_COV(rot_owner_auth_slot1, otp_ctrl_part_pkg::RotOwnerAuthSlot1Idx)
  `PART_MUBI_COV(plat_integ_auth_slot0, otp_ctrl_part_pkg::PlatIntegAuthSlot0Idx)
  `PART_MUBI_COV(plat_integ_auth_slot1, otp_ctrl_part_pkg::PlatIntegAuthSlot1Idx)
  `PART_MUBI_COV(plat_owner_auth_slot0, otp_ctrl_part_pkg::PlatOwnerAuthSlot0Idx)
  `PART_MUBI_COV(plat_owner_auth_slot1, otp_ctrl_part_pkg::PlatOwnerAuthSlot1Idx)
  `PART_MUBI_COV(plat_owner_auth_slot2, otp_ctrl_part_pkg::PlatOwnerAuthSlot2Idx)
  `PART_MUBI_COV(plat_owner_auth_slot3, otp_ctrl_part_pkg::PlatOwnerAuthSlot3Idx)
  `PART_MUBI_COV(ext_nvm, otp_ctrl_part_pkg::ExtNvmIdx)
  `PART_MUBI_COV(rom_patch, otp_ctrl_part_pkg::RomPatchIdx)
  `PART_MUBI_COV(hw_cfg0, otp_ctrl_part_pkg::HwCfg0Idx)
  `PART_MUBI_COV(hw_cfg1, otp_ctrl_part_pkg::HwCfg1Idx)
  `PART_MUBI_COV(secret0, otp_ctrl_part_pkg::Secret0Idx)
  `PART_MUBI_COV(secret1, otp_ctrl_part_pkg::Secret1Idx)
  `PART_MUBI_COV(secret2, otp_ctrl_part_pkg::Secret2Idx)
  `PART_MUBI_COV(secret3, otp_ctrl_part_pkg::Secret3Idx)

  // Mubi internal coverage for DAI interface access
  `DAI_MUBI_COV(vendor_test, otp_ctrl_part_pkg::VendorTestIdx)
  `DAI_MUBI_COV(creator_sw_cfg, otp_ctrl_part_pkg::CreatorSwCfgIdx)
  `DAI_MUBI_COV(owner_sw_cfg, otp_ctrl_part_pkg::OwnerSwCfgIdx)
  `DAI_MUBI_COV(ownership_slot_state, otp_ctrl_part_pkg::OwnershipSlotStateIdx)
  `DAI_MUBI_COV(rot_creator_auth, otp_ctrl_part_pkg::RotCreatorAuthIdx)
  `DAI_MUBI_COV(rot_owner_auth_slot0, otp_ctrl_part_pkg::RotOwnerAuthSlot0Idx)
  `DAI_MUBI_COV(rot_owner_auth_slot1, otp_ctrl_part_pkg::RotOwnerAuthSlot1Idx)
  `DAI_MUBI_COV(plat_integ_auth_slot0, otp_ctrl_part_pkg::PlatIntegAuthSlot0Idx)
  `DAI_MUBI_COV(plat_integ_auth_slot1, otp_ctrl_part_pkg::PlatIntegAuthSlot1Idx)
  `DAI_MUBI_COV(plat_owner_auth_slot0, otp_ctrl_part_pkg::PlatOwnerAuthSlot0Idx)
  `DAI_MUBI_COV(plat_owner_auth_slot1, otp_ctrl_part_pkg::PlatOwnerAuthSlot1Idx)
  `DAI_MUBI_COV(plat_owner_auth_slot2, otp_ctrl_part_pkg::PlatOwnerAuthSlot2Idx)
  `DAI_MUBI_COV(plat_owner_auth_slot3, otp_ctrl_part_pkg::PlatOwnerAuthSlot3Idx)
  `DAI_MUBI_COV(ext_nvm, otp_ctrl_part_pkg::ExtNvmIdx)
  `DAI_MUBI_COV(rom_patch, otp_ctrl_part_pkg::RomPatchIdx)
  `DAI_MUBI_COV(hw_cfg0, otp_ctrl_part_pkg::HwCfg0Idx)
  `DAI_MUBI_COV(hw_cfg1, otp_ctrl_part_pkg::HwCfg1Idx)
  `DAI_MUBI_COV(secret0, otp_ctrl_part_pkg::Secret0Idx)
  `DAI_MUBI_COV(secret1, otp_ctrl_part_pkg::Secret1Idx)
  `DAI_MUBI_COV(secret2, otp_ctrl_part_pkg::Secret2Idx)
  `DAI_MUBI_COV(secret3, otp_ctrl_part_pkg::Secret3Idx)

`undef PART_MUBI_COV
`undef DAI_MUBI_COV
endmodule
