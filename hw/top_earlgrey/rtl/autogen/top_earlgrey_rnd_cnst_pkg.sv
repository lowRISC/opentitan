// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hF45DEF7861
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h5D294061E29A7C404F4593035A19097666E37072064153623855022D39E0
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hFDB92558E2D9C5D24440722325A93144
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h6FAF88F22BCCD612D1C09F5C02B2C8D1
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h79EE911CE801484BA8373086F9DD4EEE
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h7B93136F
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hAF33379628B29DF3261A1E1BE933AB38A840EEE0
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h0738F30D9006289A1D7D9D0CE1DD7D7C
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hFE8F673FBA39BB679D58AA91AEB2691C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonSramLfsrPerm = {
    160'h25DA5869DC96FE354F1DA55E9123CB082C63B331
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h369AE283EEC5E43D4B16446726A27B8F
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h1A07EB42A37DBFB7BE9BB6E69A7D3C5F
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h096F534D
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hC0FB0F38E6BD6744364B005EC493761479F5173A
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hED204633871CB178
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h99B01E35560F2EB97E3047685D6B7BD8,
    256'h7B029229DA078DF923F7D0F46154C34BA9D43C734AF2A1EAA8E0F3270944E4D9
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h7D9CF783C36C02E6CBD0C89A7299BAC2,
    256'h45B9FB80C85367BB5E53C511341509877FB72286F4E9E3047871A354AFAD126A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hD6E49C544BA9DCDFF0245E84D6F5F03ECAEF7217
  };

  // Permutation applied to the LFSR chunks of the PRNG used for masking.
  parameter aes_pkg::mskg_chunk_lfsr_perm_t RndCnstAesMskgChunkLfsrPerm = {
    160'h46FA4BD6DC82BEB0A4E30305AA371E9C64E2BF26
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h8536E02C38ED5EDF
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h6A27354364AD3BF532784C2725D903EE,
    256'h51F44FABB76F9FB3B2FF7145729959F821AE81803E317863C98B30854D042A6A
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h239B10B10987253B015A36F15153FE5DCF92F46F
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hCB8BED0D3E48713DE5986D0027D13A3A480B63B97279D8D378486795DE27F2CF
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h8127B8EE31063C01E9BE104C7777ECC6D68E333FEDDEAC133F24DD2E11738CEB
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hFCC7CC4EC8D98B59E767A253B29311C3E284411EE572A3934FFE951D3B79C1B3
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h18800440BD414D266DE08FC479F858040892B0F3729F7AB9DAFE7F2472FB41C8
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h653FADB4AEE4626498A4C647603C2154BE52121D214556318C84C8EC175DAB2F
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hD5C72146D889ACA6973A13272144F3EEFEEDD9D57E3F829A880463A023CA0C5E
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h7663F6D1FBE7E4402C0329CAC3B7D06751F2882DF8F3259134067E7A112FFDB3
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrHmacSeed = {
    256'h0BC5F1A8862845852761603352213B7A034816103A781D0A4F5A0A911C1BCAFE
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h63DD2AF7CA1C6AE78EFCBDC6ADA112F1235EE7DBA5042C13061068C02CEF00B7
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h56289223D7E05DB35983FE5A262A6E3AB1655D42B3090AE475A2DF4171FDFD7C
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h3A1955E3D4549F3608232D03F93EED0F,
    256'hE9D1B1F891DCAB64F5A52883A710B72B92E47F6E0845F450EAD8F3095FF32C32
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h220E25BA7743095F2C1194FB74487A86,
    256'hB6FEE0311AF608B7123F603C251A36AB2E658548C5420BE549DA272D96AE771B
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hFE8C330CA072829F9970F91074501568
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h0CB942155264F8C121B7387A0A07DB44
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainSramLfsrPerm = {
    160'h2BC503FEE4EC68862F5C4DB196CC15DF82A1C8CE
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_lfsr_seed_t RndCnstOtbnUrndLfsrSeed = {
    256'h044C7BD9E98EB2847FA1A35F74A8586D23E3BD765866C6F6363A02ED345973CF
  };

  // Permutation applied to the LFSR chunks of the PRNG used for URND.
  parameter otbn_pkg::urnd_chunk_lfsr_perm_t RndCnstOtbnUrndChunkLfsrPerm = {
    128'h0C12F0E2B9EA5A371FD0F691CA53BF25,
    256'h7B7531E119CEF75B206A2CA62F4D02EE4A4029144FE8521D5F36637EE6805C7A
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h5A0D6E7185EAA2E0
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h3AE54E9E45DA6E662FB69C3AAB936B41
  };

endpackage : top_earlgrey_rnd_cnst_pkg
