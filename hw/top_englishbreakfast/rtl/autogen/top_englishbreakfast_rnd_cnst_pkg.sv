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
//                47496257290787239787852990649372780135330843464066774986444696694703339830170


package top_englishbreakfast_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h75867E60_B021E247_699D7BEF_A2EACA5E
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h9E86B268_B82B10EA_8E913C65_A10E10DA
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hA910CD93_E9E8DDE0_3E8AB0F1_F4225B70_DE66AE2A_2D2CAF52_1284D078_B2442C4D,
    256'hCDFFFC13_6EAED4BF_1A600233_980BC4CF_2116DB51_EC10B747_B9011D99_F556B893
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h842A91CA
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h1977A5BE_3574F120_58F04F5A_A09286E7_9171659F
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hBB789515_11213905
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h1231AAA3_D2B9ED1C_05893210_3E71D536,
    256'h0DECD359_406B35F1_63C98331_DB9E4AB5_A425C0AD_6FF2C166_9D9FBD4E_3E3A1CBA
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h131363A5_4D4762EB_12AD17C5_FA29FAC3,
    256'hF2BDB5DC_D35EF079_21A70602_45A0CA68_496CB337_97B3FCE1_ED0E0F64_28642A95
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hC880914B,
    256'h8567E2FB_12CE5455_E5387CC1_49C106BD_836A7311_D59DEF2E_2061B606_9E362FB5
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h046C591B_8E1E6F58_87256151_158D6002_7A8B0953_562E404F_68754D29_67053193,
    256'h81222630_2B692083_1D98657C_8C112810_5C48336A_64909491_073A9B89_885B3F8A,
    256'h23741872_57634139_863E457F_661F7021_3D6D3754_8F142C0E_329D4913_2777420B,
    256'h3479629F_039C1C76_2A01952F_555A0F5F_476E827D_0D241799_354A190C_92524C3B,
    256'h851A9680_7B5E3C4B_78849A0A_44003812_7E9E464E_5D167173_5036066B_9708432D
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hF8B34D3A_036354A7_212F4AB6_85058803
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hBA2F9679_EA462313_7127EC6E_E39AA98B
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h7F39F9DD
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h9AEC76AB_F040D80B_F3B8CA4D_B75044F4_5E50D65A
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h99151663_6BF59DB6
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h8CCD043D_5F2DF70B_7B0547C8_245DA916
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h4B111053
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hC506042F_EE9CAA76_5FB937A1_68E84453_C29DB785
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hF341D8F6_9FFAF435_E5D3C0EC_DD694B90
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hD7FB1168_378C3136
  };

endpackage : top_englishbreakfast_rnd_cnst_pkg
