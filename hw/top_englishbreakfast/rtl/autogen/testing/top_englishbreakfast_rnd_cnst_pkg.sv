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
    128'h2D2CAF52_1284D078_B2442C4D_CDFFFC13
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h6EAED4BF_1A600233_980BC4CF_2116DB51
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hEC10B747_B9011D99_F556B893_842A91CA_FC63CB10_B9446016_33A421AC_E20B50EC,
    256'h6BA7624A_9F75EE12_041D292C_75940B51_257E2224_BB789515_11213905_E9CB853B
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hC8E152BE
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h88B3D463_55372701_A8FEFA57_2238366D_CA06536F
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h654D0F66_FB6FC362
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h322BDCE4_8CFADC95_B2069B2B_82303E2D,
    256'hD1D39ED3_5A15819B_97FA26F4_EE10675A_B6D04791_F035D490_254AC617_FBBB048F
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hEA6D01EC_7CE3B436_AA6C9516_45D1B7B8,
    256'hC97F4EFE_0D417018_A1F3ACF4_46614B2C_4BA7E782_22092BC3_C8A7DB5E_4A3D5705
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h46437EA1,
    256'h9C961290_CC380044_B6A20A92_0684BC78_4B3C5EC3_F27BD1B3_F4FF8071_C1B01AD2
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h29308660_71203224_8352973F_099A2F2A_8A787389_614C6E4B_04626F8E_0588878D,
    256'h673A4208_15640066_13441B56_57011138_06287A46_935D0B4A_7F772B7B_3425720A,
    256'h989E3616_7935439D_404D5102_6831705F_5C948122_50754E5B_80908B6A_92821927,
    256'h0C7C230D_9B0F0E2D_41589C3C_543E8545_3B531C1F_47213D49_3774917E_63127D14,
    256'h591D6510_264F6D84_17695A07_39965503_2C9F1E8F_1A482E6C_6B953318_8C99765E
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h31494F63_E5134A00_4E3C988A_62C28A30
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hE3A47599_1516636B_F59DB68C_CD043D5F
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h2DF70B7B_0547C824
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h02DA689F_828EE6EF_81CAFEBF_59C8DD9B,
    256'h4AE5358B_064F7873_6883D193_16477D03_35830883_F4955E0B_CD9B2D4E_C4485A97
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hB3C1A26D_4FAA85EE
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h5F205825_CAC1C3FD_A7171378_80B3D785
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hDC68B5AD
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hDD7DF168_A4066EA7_9E114B71_4B3B9D0C_8C89AC6C
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h5153FDD9_691FDD7A_990894E5_FF39211E
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h8A4528EE_6F4A10B8
  };

endpackage : top_englishbreakfast_rnd_cnst_pkg
