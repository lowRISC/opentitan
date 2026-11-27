// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/
//
// File is generated based on the following seed configuration:
//   hw/top_earlgrey/data/top_earlgrey_seed.testing.hjson


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hB7_2BE56F68
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h04F3_4C153017_9E62A02C_E61D9061_DE4190E1_69C45511_489B4962_637E5202
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h4476F99E_7B20F788_1A36653A_B70B9E07_17C91CFC_ECA84287_601DD59E_A67B4D27
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'hF9089CF2_787C6C14_B7D1A6C0_618E831F
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'hC8129E7A_4149BA28_31FE2E9F_B3B2A1D2
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'h5254F861_BA80F82B_303DA306_35AA3D3A
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey3 = {
    128'h87F0D5EE_2B8B9DB7_D82DEDCD_5992C873
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'h0F7B70F0_CB345C05_EEC8B17C_ECD69840
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'h21BAC589_DFAD65AC_00077F26_91CA2541
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst2 = {
    128'hAE8A6546_F21BC8CF_0FD3E017_1CF89FBB
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst3 = {
    128'h7AC55875_1092EBFE_7FB39F49_03AC0EF8
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'h952D50C5_1D21F7F8
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h5B3A0CA2_9BB023A1
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV2 = {
    64'h1FFDB94D_43C33BB7
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV3 = {
    64'h6926E445_55B0747B
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [18047:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'h5F9ECE1612DE6FCF215F5CC2AB60A853BE770CFD47428325B5A9D2D6492024081FE53934CAE1D79C,
      384'hA73E019FDF0F217FFD525678046C71F4B2959D9D965AF479EB2533EA295276BB9208B6F0158C37CA6B0F944AD5A2CC42
    }),
    1152'({
      64'h0,
      64'hEFE024E64F7A8DD3,
      384'h568B3882C765E3CEDF7C4775034D3CC5001E1584FFAD542D3849E3836AB57EFAF5869E6FE18E395262997F89191D6F2B,
      384'hFFFEF15C246F62B4CA0C56D51578715AD28D102FC86A79C6F49CFEC2EE84C2C39AE243733A860B9589689D49CA24BE41,
      256'h1657295871E0F57DBABBA5389FF56CE4E1329D01FA1FCF7943D57B9508A9E8D1
    }),
    1024'({
      64'h0,
      64'h4815E26260586270,
      384'hED73C3F084F0183C44DF2B2D84DC3249FBC6048325D4C625ECEEC3C7F48DA8CCDD589F9FA43AABA8DC41C649B2F9DCDA,
      384'h961F74D1EF05954A802A757289ECB968D6DFA79E839B863C691CD750D105D75C8F08D1BDF01BC57AFF34AA4E703FA00F,
      128'h37821F53C04F3AC5AD38AC646B008807
    }),
    768'({
      64'h0,
      64'hFE1E061CCA6D3899,
      128'h3325E3EE89E068352902BF3E572C2F7F,
      256'hE916298A0649A9A3F635DA665461FD9C56614CE9709298C27140B30AC91EDD6F,
      256'h4EAE10416F98EE7B793BC40A017D736A54A4A529013A6D3C39BE97BA62B589B9
    }),
    384'({
      64'h0,
      64'hCAE7A4C6DB47FF04,
      128'h64B635C7E0CAEE329DDF84E9BA7366CE,
      128'h9868385384916566880F161290B0A446
    }),
    128'({
      64'h206892C3723DA476,
      48'h0, // unallocated space
      8'h69,
      8'h69
    }),
    576'({
      64'hD62FD2D6F44672C3,
      256'h49ED0676AB1F6572524428A0879D484BC73FF007467C44C76F4B377799D1370,
      256'h74213FA290F7E13E7B043E2CC06839DB175F8287DD7E95A4D3C1C4A25C32887E
    }),
    320'({
      64'h5CE47FE5C13D03F3,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    3776'({
      64'h3D290F7CD1014763,
      256'h0,
      32'h0,
      256'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      512'h0,
      32'h0,
      512'h0,
      32'h0,
      512'h0,
      32'h0,
      512'h0,
      32'h0
    }),
    5376'({
      64'hD854345D43D7963A,
      32'h0, // unallocated space
      768'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      96'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      512'h0,
      128'h0,
      128'h0,
      512'h0,
      2560'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    3328'({
      64'h364B7D4E6F07F89A,
      32'h0, // unallocated space
      384'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      1728'h0
    }),
    512'({
      64'hEE59F638FB0662A2,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h5E1E94F7_F23E7864_ED285FAF_0C4E421B
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hEE50CE19_6AEC3A50_18111AE4_E618A30D
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h896AB6C4_AF99E539_88EE06D5_BF24E8A3
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hDCDAE583_223A4D35_36FC08A5_486180D5
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hB1D1D271_AFB2E79A_8B9A27E5_F1C6F823
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h935FC036_D947A816_0C5A8C52_B505B10D_FDCBA642_CF8B7D74_A696F14D_83BC9CBB,
    256'h67393ECF_B1E7D2F6_9338AB42_AD967D0D_5691083A_37DCC78C_C1D36C81_83AC8474,
    256'h02230D48_F7327AE0_74C125E0_77FB3727_F4ACF4DC_FCC674EA_8E6E6928_D9D91088,
    256'h40117FBF_54657BC2_D6B0EBF4_7E1A2D3A_9E39A455_DC4D7460_D82406C0_903E0533
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hF3FD37C7
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hBFCBBA99_CDB53C0E_E78449D6_81BC31C6_85254D90
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hC7CA539F_552CB801_E72BFA7C_14B730EC
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h4CC6E0D9_63F8D3B0_2804C41E_F937F6BD
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h4609F191_9A2B937E
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h3622DB93_323A85FC_310ABB3D_AAF4506B,
    256'hC9D73159_B2D6E054_59827970_E0C4028B_7480A7BB_67E1DD97_84FF3D2D_C6176A63
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h8BBD76FA_5EAA92C8_1673C10D_8AF8A232
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hF322B00B_1B8203AD_7A9C20C3_A078F2BC
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h02C766FF_863C5EC9_01E08C14_56D248AF_B3C633F1_B7701F34_61F83DCE_4AB614AC,
    256'h8E59659F_6157848D_28230825_0BF69FA7_43F41AC8_7601D517_31193393_BAC80958
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'hB67F7341_4B704010
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'hCFE9557E_16A24589_2EB75A03_1F039958,
    256'h4014D2BB_0D288C5D_DA6A7FC8_FF774A33_3ABFB157_F1E4DB24_60502E0E_027399EA
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h2B7E1912_ABDE6A98
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hB0874B3B_81D4A4C6_55C7D59A_9356F3B9,
    256'hE02AD067_D3498B63_2825DC40_F961477F_260EF13E_DA0E8DFF_09E8172A_FB079262
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h349E8A97_68E068FE_F4C2CD78_F01B68BD,
    256'hBDE1ACB7_511021D6_717E7FFB_3222F4CB_9548019E_A503B216_A667C540_D87D39A4
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h93D10853,
    256'h67C1FFD2_16660A8B_DC0FFA52_FF55AD2D_E2836EED_C72651B3_DD41A60E_9C3BFC12
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h60963878_97408A4E_342D9072_204F616E_6A4B683B_45778B52_99851286_013D218F,
    256'h3E475591_9E8C6676_257D7351_154A3162_1C9F753A_53930D32_8150801E_58560846,
    256'h299C892C_2E2A8E64_79370469_7A747143_0F0E8200_5D6D5407_140C9528_1F134439,
    256'h1D670688_4C427C27_7E1A5E5A_9A0A5998_23225718_16330B9B_5C2F1705_027B8D87,
    256'h2B5B0930_4D497094_1B7F1910_6F921148_633F3C9D_41246C03_26655F36_3583846B
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hA85C0013,
    256'h101FF789_D8256A09_51B9A488_8318EC5F_F924CC41_9C51C152_438A65DD_B7C3A2A9
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h24B052B6_E58ED705,
    256'h39C80930_C2515930_2EB8B6B0_91D244DC_D0004D35_20FF3FA4_510DCF6C_C3E368B9,
    256'h519085A2_B95F4E33_46347883_C9281164_AA1035E4_664ED46E_551E2A8B_01285DE2,
    256'hF5868D65_C44888A6_BCEFA45C_061BD832_4C8C238E_04507721_8D92F4BF_B3290C42,
    256'hEF191A9B_55B47117_6835555B_C88B62F9_BC8FBC39_5E180846_1D946B55_A25A3214,
    256'h1DE65969_52B1F435_D797CB12_AC1F3ACB_E0B8E86C_80281C9C_51678612_56838078,
    256'hF6942BE8_37C08B15_A641C05A_B26529B1_4B4FC486_92BAA8EA_582C7AA0_8C47A17F,
    256'h9EE365F1_52999BD6_DE1968EE_73C6B410_8A1589A7_9F4F8305_096BAB38_55B04ADE,
    256'h9A194F90_93286ADD_40C32A9D_506F9C1C_110E0A97_92C06C7A_8331B57B_3247FBA1,
    256'h06201EDB_98A54AAB_6178CE1A_8464F667_9D41C9C5_DC29E390_EDD52D9F_6761D27C,
    256'h91259463_0E57EA55_CE818EE9_0C2C08DA_5276CF4D_8A03554D_37C4F0FC_5D322137,
    256'h851D4A41_31B86639_1D6A6072_9FC0A912_1B014E25_50A3BAA6_28FC2608_9A20DA97,
    256'h8ACFC5EB_0903C573_5E709D26_EAAD0C92_4908D5AA_33C892A0_986E9B57_14C5B412,
    256'h28588A67_D8E71817_6DA8FADD_4C5B491B_0AC78C44_E4958235_ABB31CD8_600812CA,
    256'h1F0795C3_4A334795_D5E1632D_09E851F1_14DA0BF5_AF62AF71_071E8A88_5A7B003D,
    256'hB1C235A6_30EA6735_9366D405_12631459_C63D3976_6B11C5BF_8322C11D_FB5253C0,
    256'hDC7C7018_BB45C302_C9715713_5C8F06ED_6EBF1649_A574132B_2148541A_640B2EAD,
    256'h9340CA44_9A92CEFA_75B859A5_778D1387_1ACAFA6A_37201265_F88226F2_B16A7F2C,
    256'hD0E8CB74_03DC5605_186598A4_1561B0A8_E23AA72B_8A30DE77_6C61FAF4_2F2094F8,
    256'h5C89D421_62A4B20F_47AC1A76_EA94CDC9_A2A93486_C4C5AD3B_9074545E_F9E6025B,
    256'h17340ACE_7B8281F6_26BB0C2A_595B9F04_916E5397_2AC3DD43_9404BB5D_C2041158,
    256'h90A46302_5B7D5FBE_0E945834_00E8E36D_D386035A_6CD428A3_759DFEB5_0679E975,
    256'hB82A09A2_653D6FE5_5F03BDA8_72A82DC0_4FA4619D_96F1A441_1147EF58_41F4969B,
    256'h1C3658C6_ECA080E5_BB941401_26AF2304_6A0404AB_F9188295_2007470B_97947062,
    256'h6DA20E11_01581E6E_3A489B93_1E70ADCA_4BD6B6A2_E24162E8_A0680653_84B2AA5C,
    256'h531BFE41_C1EF1407_17582AF1_158D4EC8_36F24F9F_9CC882C1_848B387A_772A5E58,
    256'h3E110507_6075B9C4_99E77DFF_2E2819CA_3E645E03_A8386251_9B653A88_C4D42B18,
    256'h7DCDD0C1_AB43EE19_213466AB_53F553B7_920660CA_4B5F3B68_1B41E51A_030F17DA,
    256'h1C084A03_8BB5590B_71C95194_8F1CD358_868B9CC5_921DECBE_CC682829_1D4BA09F,
    256'h064C188C_44160C5D_4B6ED201_225C6661_6402FBA5_F5335952_7EBD0029_F7E5CB98,
    256'h1FAA2617_3CD2380C_F28F0AE7_9A4EB718_5A88E676_981A6408_A6AD64B9_27A14B51,
    256'hACCCA130_8874627F_4E72DC21_9ACF9472_C5412F0A_BAC39D87_BC765D02_6EDC50EC
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h2A60B3D9,
    256'h85B92EFD_07B7ADC5_CFECC252_10176BB4_737347A2_EAEEDDC5_518E2E1D_BFA516E8,
    256'hA695B863_BCD9B680_028DE915_A051379E_8D371757_07D7713E_79DAC47A_1E4AFFAF,
    256'hB204EFD9_2199B87D_EEAF9393_72565AD9_2F77EC07_793F2F1E_FE52D58F_9C48DBB6
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hA9636994_88BA11B2_90C851CC_69FBF656,
    256'h0C27E14E_E43BE64F_4C34BD5E_BB37600F_E68F4B4B_B89D42E6_1728C7C7_86741473
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h73456F80,
    256'h1EE6C4A4_039CC66A_7B6FCBD8_8EE99BEB_7593D964_F225ED6E_76B3DFE2_732DDFDD
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h00C3_1D36BA55_6D2D4491_9919C5EC_5186819E_874788B8,
    256'h46078346_EC8DBA99_24F8E57C_3C927180_D8C08AE8_470AE395_78B90180_210203A6,
    256'h6C235009_D4B4005C_0FC948FA_A0221C6C_A8E9C3F3_602D7713_5682160A_42207989,
    256'h3B9358DC_260C01D8_537D5151_ADA1DBDE_05571584_24518A7A_E374EEA0_17A66172,
    256'h1029390F_5F618B6A_31DAD88A_A08954C3_88CF5BCC_25DA094D_362DC6B0_A05ED4CA,
    256'h9444078D_792BF434_31860B28_403B0208_F2C6902A_A98D66E4_A8D10262_DF86C5F0,
    256'h5468864D_25150F52_79EBF175_2FAD1EE7_5008A2C9_961F971A_60EC12F3_38B65913,
    256'h8490D351_28DD6E7F_37861907_29F2612D_826A242B_CD0598E8_2124258D_56D7A41B,
    256'hEE831240_D9D4D164_695E0861_774F18E6_71CB4914_5268CA5F_F2B705C4_B93F490C,
    256'hC7CFE4AB_3076FA19_1223C191_E93202AC_4240C2C6_67CCD9A6_F077CE4B_172ACD21,
    256'h9F7674CC_97F844FA_21794F3C_598B4E28_51D4CB83_42ABCBA3_4733B051_55311CC0,
    256'h34A299C1_72F798DE_09E2AA20_99C8AE4F_5AD936FA_3DB26956_6AA9692D_F82A2ED1,
    256'h521C2E28_69DBBA70_85735ED5_26F2D09D_159ADE20_B9EE80FB_4A02C2B1_88D88C81,
    256'h575A84A1_384D9B41_A6E2B5F2_B14B71DF_E1EF3239_F51F40BA_D9644209_84B17C97
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h99463B5F_DE2CC5E4_098F1103_9D33C6AB_938AA8B3_E3ADEFA9_E93A2988_A1D9E782,
    256'hB25578D2_50A77F6E_AF63C1C4_F4FFDC56_6114190C_6D3FC8D4_D0F3BB62_5C1DCDB5,
    256'hA0D71742_C996A51A_23A6714E_ECB8AE59_7B3408F8_9E8C189C_44FB3CB6_837A2560,
    256'h804BDFE8_6997CCCF_77727DF0_869581E0_6B1C3707_356AA3D3_2854F1D5_1B9A58EE,
    256'h2FE6C301_1FD6C72B_68105DEA_B9C2B727_9870F52D_90AA2A92_04948E49_6C30437C,
    256'h0F65A2F7_F206BDB4_9B0D051E_E5BA2EC0_8D225A15_4A894753_ED911632_02CA0BAC,
    256'h74FD64DD_8426764F_DA5EFEDB_00F60E0A_666F1345_73FC5B24_D13E3D12_CEB15251,
    256'h8BBF79BC_CB4D8548_4041FA20_395721EB_4C67F9A4_E136BE87_B0D8759F_7E3138E2
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h1131_30151D2D_622F1903_6B436E1E_B16516A0_D678DC70,
    256'h06BD8B0E_51E00451_307633B6_C416B471_F4322B6A_5918CD25_2B4BE403_7039496E,
    256'h9449F21D_BB0332DF_4EF0546D_E830AC50_4388F3F0_22B474A3_0B10E769_885D0A4F,
    256'h546BB9A7_8958CDAE_566C172C_10C686A3_66DF4BBB_604C32F7_C362BB7C_78118178,
    256'h2BC04F01_580BABAA_E7EB7460_7F0A9A21_4DD2E713_84943815_10512701_44829100,
    256'h99D045B4_933BD568_CBAD5565_2EF6F2E6_A25E8895_B097118D_B2BC5761_BEA8D2A7,
    256'h1BF22835_7022E3C5_11E1C4B8_802AA6C8_87F9ED35_E6499B13_89B2C84A_ED50744E,
    256'h10024086_FDE40D52_55980A96_0522A9A4_825D4121_AF6AE3A1_8D4F22BA_81E422C9,
    256'hAE02D52E_8259CF43_E2FC6EAF_3252A98C_DB912C33_228EC7D9_8FBA7588_EC02BF83,
    256'h80E4815A_8828D0BD_98919377_B9B522FE_9D316B31_2908C2E6_CF0D2596_C50AB080,
    256'h42FF0FC5_C2AFD4BB_C844663C_4204811B_AD98DE3D_3D9A814A_9942228A_9DB29D68,
    256'h010721CE_BEBE75AD_C5258539_6D08E512_AE14A1E1_1A481AC7_6D077072_613A78F4,
    256'h344A359D_D5368A4D_E232A806_E62C0648_B286E78D_4E60EA64_C93EFCC1_921F6EF6,
    256'h19AB7261_630E269D_95B612CD_42D38120_64732B24_E1065317_A413E797_4BB4BE0C
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h518D44F0_E1829B14_B8F03026_BF6DF011
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h6AF77D3A_A25C37B1
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hDDC04F6B_EE51CF42
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hA8A55068_9DCD23E7_73D6F3CC_A3B6DFAE,
    256'hD620138B_86CA79BF_8D3D8BF0_E5121FD7_17030A6C_C56464E5_E8850746_65E83842
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hC0B4D05E_1C78D7B4_F73FF309_49D8C1A9_DCA2A251
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h44A1CB70_17026D90_DC96907F_05BAFD75_1E56126B_50AD5C68_DB4EA7C0_3669D35C
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h1FBB82FD_BDD0BC15_B52BAA0C_5057CC23_28956934_A178AB4A_E3A7537E_EE6264A3
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hC067F0AE_8787028B_CC21E3FD_65CCF384_275C1342_2A2D18FB_3DA8DE1F_07E850B7
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hF1BCDB08_CC744A0F_36A428FC_3CC24813_17D64302_5D14CBAC_E9276534_C3AFD9BB
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h620030B2_6306197D_A9B6F314_D782FF5C_AE517B83_BBECD428_D182CC47_61BA188D
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hD84C8710_0D52E6CE_500195F4_031A37C1_77007340_0F05C664_F9698168_48933729
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'h3EE24E42_5434B908_AD83ED89_E532E2C3_B2704095_98650110_9446F3A0_A9AF793B
  };

  // Compile-time random bits as a field entropy alternative seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeFieldEntropySeed = {
    256'hD3A550E2_C0DEE27B_296CE2BB_F63B835A_CC5DA048_7D9D30E5_641063D8_78E241CC
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h07701212_AFFA2BFF_92B10DC6_E323AFFD_519436E0_0287ACA5_07D0D167_BC3FEDFD
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h7B457A92_9BAAB0E7_E99F89FD_4683681C,
    256'h3AA7D0C5_0C1A09B0_4A371A24_B6E7A444_11DE548F_89387F2D_3572188F_580860B8
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hD170B5B9_A247B228_DFD232FE_16037747,
    256'h6658C881_4A96E3CE_C90ABED0_540E2B91_CA1F2DA6_A318F2D3_FAFFF231_021D568B
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h26F8D486_E5E70556_6B6EA0AA_9B186983
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hD70007F3_6D01D4B2_1FCCBB39_41A97330
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h37B5D2E6_AE0B3DDC
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h322E0425_C854EE46_B72302B9_02A67FCE,
    256'hFA6DF654_580831C6_4BEC6857_43E37819_8E9E0E96_7D3D9BAF_CD5DC85B_9740D2EC
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h9AD866C5_81D41063_B442D7CF_6A5979B0
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h19877C59_A30EF573_130B1C47_B66509A3
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hF243654F_EC4BF9F3
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h6DE50964_3B06DB74_4C928C4B_E61A783F,
    256'hDAFE3668_C24B35AD_7E0D4103_2884545D_2797AEC7_390A9363_F5CA72E6_AFF1DC08
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h8D083101_E7C40F2E
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hC5893089_7B610839_1BE560E7_57B29BD2
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hE361E2E7
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h74447C84_747D8104_9657E37D_D27F1A45_4DB9AD4C
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h88729280_54B7C19D_5993EFDB_9C78AB30
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hD9525B3F_86FA2EBC
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h65E81F10_79CBD740_B8DFE15C_AC06D966
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'h9B5759A8_B1F53F0B_56174441_0EE61335
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h74BB7DA1_5BEC38BF
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'hAFE35E13_AEC6AA76_8AE09BD5_5B31668A,
    256'h11EE7326_1BE4F81F_74C425B0_2F2D4590_F5F634D2_2CEFC8A3_0D17DF60_40524A71
  };

endpackage : top_earlgrey_rnd_cnst_pkg
