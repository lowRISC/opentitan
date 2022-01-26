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

  // Compile-time random bits used as token value if the token is not valid
  parameter lc_ctrl_state_pkg::lc_token_t RndCnstLcCtrlRmaTokenInvalid = {
    128'h03A0B091DC41D062DD10CA2D7B93136F
  };

  // Compile-time random bits used as token value if the token is not valid
  parameter lc_ctrl_state_pkg::lc_token_t RndCnstLcCtrlTestUnlockTokenInvalid = {
    128'h0EE2A465FD4DABCBD877AFB6BCFEED7E
  };

  // Compile-time random bits used as token value if the token is not valid
  parameter lc_ctrl_state_pkg::lc_token_t RndCnstLcCtrlTestExitTokenInvalid = {
    128'h3C91917516D51A2FA4400ADC2669E253
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h5CBC7746
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hB9702781CA9DA90E7C883543EEEB6389F2D5C989
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hE21FFDF7075A864CB4DAAB803225B91E
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h47E71B5C0205AE5E5FEED81E0CB15451
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h1702EF71
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hA593F517835DDCD09006F47B03EA5960AB846DF3
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hD417DF2F55255E182EFED724CF837046
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hF70A5B088FEFBC18548DFCB2FD145395
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h102F4C28
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hEBA451575157868B9F266EFF382C017D989C7094
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h4AD181A3BE2D2767
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h9D7E68EBC6ED5B034B3E40AE040CE5D9,
    256'hAD18ACCCB12667A213E1D3BF5577778F438D12A0219B1F40EFC5512721EE9A86
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h2837D9DFCB60E8BC7431A89C6C136576,
    256'hC254780FEB5BDF8EBA84B092F239CB51D1A671A3857E0FA85CC44F699054263B
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hB978C925193F36D89ECE5F177E58B7BA1BA4DCA2
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h0B537B3A742586214D711055987E642841830732425B233624271A3B884B115A,
    256'h7C3D91379D44897A298F139E5C39676D8E62471243690A755D787F339B6A5240,
    256'h149A031C724A6B48093E0E2F1D150D1F93951787044E3F941B73822B8D660C26,
    256'h9F450F354F761E684C57188B798C96706C978000018A58469C2250996E605F2A,
    256'h65597D8119023C163063902D3120923405085485385184772C2E49565E06616F
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    128'hAD9885B9785B3FC6B67F29C1411837CD,
    256'hC7B958D6130152A3F6A1CCE0352CEE89B022FD1DB46FC92F14A53B50BAFA9904
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h15891B60C560A7FB75457E09E258C252C3083125BE14E22D044C7BD9E98EB284
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hDDA4C0A399420265983D914E80A925BC
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hD95CD1C662BDAE87
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h562CE22F82424801
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h6BC39971578C9ADD918EB1D75B40FA12,
    256'hFA3DFC195F9F8A6A74BE6E609B1B206C3EEE214D037CA02900A4513CF1852D4F
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h640DF7E2B41B9496C742974B925CE0E23CBB4C3B
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h80A8D540CE8FD0CD3D3BC1416C0834AF84DC448F6A9887A8E3ED3CD5EA91A34A
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h95EC8AA1BA59CEEE7530A14494E10193220B62D997F24A95F0C5E668A34CE097
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hF779EE523615334390CF654EC6352ADF5010157D1342BD7B2EE4C310DEFC471B
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h7236A121E1E0FF0A4FD70234BB32EA7240D7D8470E011CF1B1987A780AF5815C
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h4AE5E2CF5E723B547CB4949B21B3DECFE8F6679035DA35061952CD5387F9FB72
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h5661E47D54C36F827B99DCC91893C0CE9E8E5600260058176D17F3660EBAD942
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h4BE66E95792C3D8EAFD0BC4DE80468FD7D8490DC838E24FAFE4257BCD0D4AF88
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hE8BC8757CC921F3C920C664026717440062CA8D4D838B3501E1CBEBB834986E6
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hB9ECDE94C6064C512F50996293612AD056CBEEFC913B5FF592BBC26408E95BDB
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hA0C86B9C1EF6117215C2E6FCB683D3A9740AABD84D6481D22FE896642A15985E
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hDF2A87ABF7C57A6D06F2E1721E3A5F3B,
    256'h217D62ACF1C966C712691421CEF76350BFAFCBEBD7C3361357BEE83E46164C82
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hFDACED02DA0253D803D1CDF325AFFF8B,
    256'h5910642E0F9946CB60F5F7D233A13B89BFC3162D205B4D60C9B16A8EB0AA75FA
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h30AC79EEC48E320BDCFA32F724F82840
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h2E53C3844212490CED20E7E16F71067E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hE7BA5D88
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h026FCE91CCCCBE2D84FE50CCD9EAD4C410B79635
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h0EB63A613068D71D
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hC967EAA9FC47E9E7507D72B87001FA7B
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h406D9D57
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hDC03CC122D518F3C805643B555B125A7C7E7CAFD
  };

endpackage : top_earlgrey_rnd_cnst_pkg
