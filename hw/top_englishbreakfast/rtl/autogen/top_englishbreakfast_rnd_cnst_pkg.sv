// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson \
//                -o hw/top_englishbreakfast/ \
//                --rnd_cnst_seed \
//                4881560218908238235


package top_englishbreakfast_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h9E90F8E6_5F8CDC02_8E681EDC_B14CB2E8
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h1C9634B9_FA84FEC1_CCC9E252_5B4ACFBE
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hF1354B09_69540F0F_285312FD_274E1F61_36763B10_AEF74FEA_8020040B_2A0B515E,
    256'hD5E666D7_71EF5001_237710FE_B20A90ED_FFD46B00_CE07C1B5_411E7934_82C8143E
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h6AE2B721
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h757EDCD0_D2E4D0B4_EAE27D83_1600B8E9_06756E1E
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hC5A44F9D_C00A807E
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h80E79CF4_8B437E73_292EB407_C40D04FF,
    256'h2C3B476C_F9368E13_6D55D650_F912F1A8_82F89D5D_877BAF1B_AB18A819_A58D9285
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h80D40CBF_860E2277_9193A5F5_4B4D997D,
    256'h60D3F2B9_A3C4AF47_54497F09_BCA214BA_3BC1D6AA_073E5C86_EF8F254D_EDB29180
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hFF657FC2,
    256'h9427D0F4_8AAD106E_3859890C_09023558_95A38418_FA02E124_5E46FAC2_4FA1FC04
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h9D12152E_8B3C0F99_008D9510_71673B88_2F61057F_1E7B1668_5439498C_5F34735A,
    256'h4F59705B_7437751A_369C0C64_291B4B2C_879A657A_9B254A20_76401D24_6D06698F,
    256'h52770103_57433197_48324218_9019932B_7C9F274D_08603A35_8545621F_2A81500E,
    256'h923D5178_6C2D4602_1C6E445E_589E7280_3F66418E_6B6F6A17_0D565D8A_82237D79,
    256'h94980933_0B4C530A_91868463_89133830_04832696_3E4E1147_555C0722_1421287E
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hA84AFD11_0E65E2C0_9D401249_1AC45C2D
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h07799E69_9C02A50A_EE3B25AF_703B953B
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h72C25ACD
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h70F1C202_29AEF41B_AEC26351_432B3283_CB33FBBF
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hA055CD15_3E14AFCF
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hAF2B8B9B_A0EEEEEA_B949B446_2A2E7E3B
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h88F2805B
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hC19B5091_071AF9EF_D36FC952_E8A99300_AF097756
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h6AEABF22_75AFC88A_1D1273B9_9C6D2D23
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h9F28888F_3EF00FC7
  };

endpackage : top_englishbreakfast_rnd_cnst_pkg
