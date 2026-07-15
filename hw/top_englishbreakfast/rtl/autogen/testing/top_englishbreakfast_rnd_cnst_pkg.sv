// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
//                -o hw/top_englishbreakfast/
//
// File is generated based on the following seed configuration:
//   hw/top_englishbreakfast/data/top_englishbreakfast_seed.testing.hjson


package top_englishbreakfast_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hFC63CB10_B9446016_33A421AC_E20B50EC
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h6BA7624A_9F75EE12_041D292C_75940B51
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h257E2224_BB789515_11213905_E9CB853B_C8E152BE_7FD8A464_E8062CBC_DE6EB50B,
    256'hCEC7E572_26E6B0BA_EE935A92_CC487A08_74A2330C_E60A38A0_61E3BB0C_D2070863
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    64'hD8654D0F_66FB6FC3
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    128'h322BDCE4_8CFADC95_B2069B2B_82303D2D,
    256'hD1D39ED3_5A17F19B_97EA26F0_EE10675A_B6D04791_EC35D490_254AC617_EEC123D8
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h1673563F_29E7D4D8
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h4116C95F_9D7BFE5D_0750398A_60DBB6A2,
    256'hC1B30163_2315D4FE_AB26AF06_D7CEC551_19852F37_2E971EE8_222092BC_0FF788A7
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hECDC90F9_9D98234D_5F8BF4F0_1E72BA16,
    256'hB556E37E_7CA940C9_2DB68CA6_399DB867_20B315CF_49EBE107_D0A8B510_0ECE4125
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h10651DC9,
    256'hD35928FA_25C625BD_E86E927A_438E3F39_A6778B9F_7DA87872_B1835B1D_F71F311A
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h91472C21_2F751674_0E673203_3B4A5F66_8B2B559D_6171566F_730A1B8D_20405C5D,
    256'h5260281E_5A0B866A_9554279E_902E498E_64940C7C_303E2265_974C0012_8A43419C,
    256'h69187F7E_08709F99_1405481C_3F454D37_13380911_6D8F7D5E_84928593_5B257610,
    256'h532A3101_1D269607_367B5102_8C23780D_509B6E83_069A1789_29885724_684B3915,
    256'h797A6C2D_876B8180_63340482_62774F3C_353A4442_9858590F_723D1F33_4E191A46
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hF6CB453D_226BF341_D8F69FFA_F435E5D3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hC0ECDD69_4B90D7FB_1168378C_31369349
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h382CFEDE_1BB42992
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hE87D6D9B_D9C23D5E_CAC9400C_0FC65FAC,
    256'hD73E93FC_4B052E1D_46E1986A_F81E105A_795885F6_A936E8C2_C865889C_F4DD08CE
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h0894E5FF_39211E8A
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h4528EE6F_4A10B8A9_0C5BEED7_801093BA
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h68923496
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hCFB7895D_042AE224_8C01ECD8_783EB457_F9A758CD
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hF5184E5A_C0E0AE93_B79AE228_DD17836E
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h952390A7_3649F56D
  };

endpackage : top_englishbreakfast_rnd_cnst_pkg
