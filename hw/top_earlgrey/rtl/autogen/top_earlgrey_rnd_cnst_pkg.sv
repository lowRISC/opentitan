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
    64'h4440722325A93144
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    64'hFDB92558E2D9C5D2
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    64'hD1C09F5C02B2C8D1
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h2BCCD612
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hB265E7161A57CD840E2D9B32B38A840DC1C7F6BB
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h9FBB73A9BF8C393C12965C7DE10023EC
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    64'h60C06703B494B3FF
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h738F30D9006289A1D7D9D0CE1DD7D7C
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hFE8F673FBA39BB679D58AA91AEB2691C
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hAE24AF11
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h25DA5869DC96FE354F1DA55E9123CB082C63B331
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h4B16446726A27B8F
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h725022AFED8C3F0C64F132A9FC5D1745,
    256'hD64EC881FDED0E5FE8D9F8DEE8215810DEB1848952D123D552F36AA086A2F99B
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hA77B61ACD1356DC20CD7DD118E18EDEB46B20763
  };

  // Permutation applied to the LFSR chunks of the PRNG used for masking.
  parameter aes_pkg::mskg_chunk_lfsr_perm_t RndCnstAesMskgChunkLfsrPerm = {
    160'h311A5ECD60FF1F145C3265ABEC8D303A85AC3B74
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hA26D06FED461E43E
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hEDF8195A833EB78D252D435C8B301B7B,
    256'h2BC36B6270C52908AE9B07EB9F615EE3F51444E641509876ADFC28647F9E304E
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h97CD1105DCED6F9458F02A54BDF9BA9BC60A6184
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h3C7A34558CCEC99F160326DB309C3ED8635B48D5DD14C50A053DB7469BAC5612
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h81A3637187C027B6ACA8E4FFC89A3209A1642741192E3979E50F4B7302BF908C
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hDC165280C0509A5CBEE310112A22E896651CDF06599BF6FFC17FFF937DE17023
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h36C5B3D0A873F50B0E273058CAA5291BD06F88A44B8243CA1A45B215CC7256C
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h44AF7C286396D54F33CEB281D957BF9ED89305D88D8D71C2CA6258CC000DA006
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hF085D06D98C25574D82449E1AFA2201F312EA264F507A75D5B610152D8465246
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hED2E99906A4AFBD4DEDB5CC59EF74E5AB14D5B983DD7598AF12E48C599DA1605
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrHmacSeed = {
    256'h198A2B804DF44B9E44E1C905DCD81E3B8ADCF2EA1EB87424E51CAA14DBFBEC75
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h710581E83789A7B90140C94645887A4457E74CD0C4CCA056411C89563D15B47B
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hA2415E162F57F8AA2CCE101E080C3A9DB8CA70B49D1050C47FA9CE86F3443C8C
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD0EC61B1BDCBC0E305B5E826EF06FF71
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    64'h3E4EF606D8CEFA03
  };

endpackage : top_earlgrey_rnd_cnst_pkg
