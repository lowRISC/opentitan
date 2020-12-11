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

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h96466A983E5346826A43628219E5A91389B9FE0D3B818E46CE7D846469A3B8E3
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hDE094CA8F1435F85E0F7489A309CBE57B77F07FF3D7297200D5AB25561AF49C6
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h12965C7DE10023EC699679EDD5369F11B49BAC9198BD1FF344C5DA2242D290BE
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h738F30D9006289A1D7D9D0CE1DD7D7C60C06703B494B3FF9FBB73A9BF8C393C
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h613E5324CBAC660746BCA7E0AE24AF11FE8F673FBA39BB679D58AA91AEB2691C
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h205AE5E5FEED81E0CB15451E21FFDF7075A864CB4DAAB803225B91E3B1A7B12
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

endpackage : top_earlgrey_rnd_cnst_pkg
