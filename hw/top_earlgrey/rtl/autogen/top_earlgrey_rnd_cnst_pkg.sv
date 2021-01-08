// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                --tpl hw/top_earlgrey/data/ \
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

  // Compile-time random scrambling keys
  parameter otp_ctrl_pkg::key_array_t RndCnstOtpCtrlKey = {
    128'h79EE911CE801484BA8373086F9DD4EEE,
    256'h6FAF88F22BCCD612D1C09F5C02B2C8D1FDB92558E2D9C5D24440722325A93144
  };

  // Compile-time random digest constant
  parameter otp_ctrl_pkg::digest_const_array_t RndCnstOtpCtrlDigestConst = {
    128'hCE7D846469A3B8E35A6BD38295BD2FB3,
    256'h66B3D62126C75EEAEB93D32F5CBC77463C91917516D51A2FA4400ADC2669E253,
    256'h0EE2A465FD4DABCBD877AFB6BCFEED7E03A0B091DC41D062DD10CA2D7B93136F
  };

  // Compile-time random digest IV
  parameter otp_ctrl_pkg::digest_iv_array_t RndCnstOtpCtrlDigestIV = {
    64'hB77F07FF3D729720,
    256'h0D5AB25561AF49C696466A983E5346826A43628219E5A91389B9FE0D3B818E46
  };

  // Compile-time random value for RAW unlock token.
  parameter lc_ctrl_pkg::lc_token_t RndCnstOtpCtrlRawUnlockToken = {
    128'hDE094CA8F1435F85E0F7489A309CBE57
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    64'hF4C3471C5DEF7861
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    64'h83D0550B80E84EB1
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    64'h2D73930D4CAC3785
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h5DEF7861
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h5F00C4CAFD73FC4AC479A61068375F38956D84B3
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h83D0550B80E84EB1F4C3471C5DEF7861
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    64'h2D73930D4CAC3785
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h83D0550B80E84EB1F4C3471C5DEF7861
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hFABD19450B238D4C2D73930D4CAC3785
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hD89F9DFC
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h26FF203D990D87C5E8A98BAFEC7506855AA99C54
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hF4C3471C5DEF7861
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h26AC29E186C1F4DC6F959D6ED08DC044,
    256'hA0F3F1519E8DCA131275DF1E48BBF964AC772E613D0320ADAEBF38552DD822E6
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    128'h4F0714285BA12D9A4DF2F7FB6D6CAA4A,
    256'h08DD5787B52422005F6A3EF6BC6C0641F79C4EBF99140CB790D894F68688ECF4
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hF70A5B088FEFBC18548DFCB2FD145395D417DF2F55255E182EFED724CF837046
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hC761467EE390FCE7275F3BCE5145A3B8EDB5F33FD64E96A5B7A45278102F4C28
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h586239C405F0E50F0C4CDF307B6CF85BD7669C05B0E5DBC9627C050E4936E54C
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h82989AA7C19175299F2746EA860D6C0DD7A42245F8E1D251D66CEF31BCE5F18F
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hAF06B42350BB6B68440934DCB834F93689FE9E88EBD53404A1D7296F0CBDB8B
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h478B95E538DE6EB34DFA33F033A4AC96ED204633871CB178192AADBB7C918ACB
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hF7B0CE3CFFDA0E9782216C0746509E39F6D4E529C9F758F873D25A17251FBE68
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrHmacSeed = {
    256'h2A0B3C4BEE57F5D184C6556972BB2473AA3CF1C7FEC9F29FDE876AA58DAB46F4
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hAA6F96B90DAB292385D4C54B84F64FC4CA34017BD3D719864AD181A3BE2D2767
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h1BC49BC3169634F35079421849A93E1372402AA2853E37CAEDA025CDA5AC342D
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hB6D4B556D89F9DFCFABD19450B238D4C
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    64'h160733E752CAD615
  };

endpackage : top_earlgrey_rnd_cnst_pkg
