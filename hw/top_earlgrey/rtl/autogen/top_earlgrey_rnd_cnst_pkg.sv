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
