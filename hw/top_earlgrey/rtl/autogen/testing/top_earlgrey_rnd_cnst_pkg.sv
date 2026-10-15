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
    40'h2F_0DB4A2DA
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h6E19_DF1DC196_75360B31_155011A8_94983052_28066435_73DE2028_258C5389
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hEB970F14_43777AA1_F10CFC4C_0B23F162_9B563D9A_0284E7A0_A8B72BE5_6F680BFE
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
  parameter logic [16895:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'hD28D102FC86A79C6F49CFEC2EE84C2C39AE243733A860B9589689D49CA24BE41568B3882C765E3CE,
      384'h1657295871E0F57DBABBA5389FF56CE4E1329D01FA1FCF7943D57B9508A9E8D1FFFEF15C246F62B4CA0C56D51578715A
    }),
    384'({
      64'h0,
      64'h6B0F944AD5A2CC42,
      256'hFBC6048325D4C625ECEEC3C7F48DA8CCDD589F9FA43AABA8DC41C649B2F9DCDA
    }),
    768'({
      64'h0,
      64'h9208B6F0158C37CA,
      256'h8F08D1BDF01BC57AFF34AA4E703FA00FED73C3F084F0183C44DF2B2D84DC3249,
      256'h961F74D1EF05954A802A757289ECB968D6DFA79E839B863C691CD750D105D75C,
      128'h37821F53C04F3AC5AD38AC646B008807
    }),
    768'({
      64'h0,
      64'hEB2533EA295276BB,
      128'h3325E3EE89E068352902BF3E572C2F7F,
      256'hE916298A0649A9A3F635DA665461FD9C56614CE9709298C27140B30AC91EDD6F,
      256'h4EAE10416F98EE7B793BC40A017D736A54A4A529013A6D3C39BE97BA62B589B9
    }),
    384'({
      64'h0,
      64'hB2959D9D965AF479,
      128'h64B635C7E0CAEE329DDF84E9BA7366CE,
      128'h9868385384916566880F161290B0A446
    }),
    128'({
      64'hFD525678046C71F4,
      48'h0, // unallocated space
      8'h69,
      8'h69
    }),
    576'({
      64'hA73E019FDF0F217F,
      256'h49ED0676AB1F6572524428A0879D484BC73FF007467C44C76F4B377799D1370,
      256'h74213FA290F7E13E7B043E2CC06839DB175F8287DD7E95A4D3C1C4A25C32887E
    }),
    320'({
      64'h62997F89191D6F2B,
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
      64'hF5869E6FE18E3952,
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
      64'h3849E3836AB57EFA,
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
    3200'({
      64'h1E1584FFAD542D,
      32'h0, // unallocated space
      256'h0,
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
      64'hDF7C4775034D3CC5,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h2096B49F_EDB97CB8_8F8F255A_4ADA4FA3
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h20AA8826_89B418F1_26854B3B_30204762
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hF66ABE7B_A9A5A08E_2368F001_5C5DD01D
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h224476F9_9E7B20F7_881A3665_3AB70B9E
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h0717C91C_FCECA842_87601DD5_9EA67B4D
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h275E1E94_F7F23E78_64ED285F_AF0C4E42_1BEE50CE_196AEC3A_5018111A_E4E618A3,
    256'h0D896AB6_C4AF99E5_3988EE06_D5BF24E8_A3DCDAE5_83223A4D_3536FC08_A5486180,
    256'hD5B1D1D2_71AFB2E7_9A8B9A27_E5F1C6F8_23935FC0_36D947A8_160C5A8C_52B505B1,
    256'h0DFDCBA6_42CF8B7D_74A696F1_4D83BC9C_BB67393E_CFB1E7D2_F69338AB_42AD967D
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h0D569108
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h44FDD958_AA5D182C_FC6F4848_075EBA83_791C6CC7
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hD9D91088_40117FBF_54657BC2_D6B0EBF4
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h7E1A2D3A_9E39A455_DC4D7460_D82406C0
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h903E0533_F3FD37C7
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hEA347C83_3F7755CC_66AC3A32_D1E3091B,
    256'h5BDA017E_1DA8A67E_6E5B0E22_D10DD81F_CBA5348F_590B877C_28B0E459_14EE7621
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'hEBEA4A3D_8F4D3F97_DA771FF9_A7651A7A
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h2980962A_A3F903BD_B8130F38_73492461
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h5AA20909_7A39EA1A_ACC863D7_B8C1EA22_D728B81C_E0868CB6_ADB4DD9D_36F352A5,
    256'h4F4F2700_57362BC9_5920C536_A13C3B8B_BD76FA5E_AA92C816_73C10D8A_F8A232F3
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h22B00B1B_8203AD7A
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h7E6DADEF_4E9DF29A_A52C98A0_182CCE0F,
    256'hE51369B0_4491140A_FF75B8F6_ED583477_0CB2B495_163E725C_F859C40B_DEA30227
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hE4F4F972_09E1802E
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h67CD278A_4A08B1FB_8396FD7B_616DCDC0,
    256'h728ECB87_66100E94_AF369547_D86DA71F_EA3E0F92_8CC2F608_55DC7936_C9181439
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hC6458B39_E1D98CCA_94295BC8_D1BE2D7C,
    256'h0A46FD34_98B33DDD_0977103E_5851DBAF_83B84F35_83B37DC2_7A05CAB0_7926299A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h929A4D7C,
    256'h630F53C5_9E65A816_D3CBCD38_40A67B18_01E64BD3_541B304E_89233922_98E32151
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h2969743E_7C75706F_342E6493_6823399B_33277E47_54104B8B_5B9E0080_4A454843,
    256'h46829560_14816D22_1C943090_658A8C62_4F88516C_4D6B442C_773B9C96_2B984019,
    256'h0B618317_05023C85_152D0418_26495838_5F0D3F0C_57799F87_2431921F_1E91725E,
    256'h9A360178_55322F5D_1B1A7A42_35091D4E_0786206E_59281363_76374171_84562A7F,
    256'h520F0A89_16678F08_97664C50_217D9953_036A7B3D_0E069D8D_5A128E25_113A735C
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h214F52F8,
    256'h78AD3EA2_CB34C201_ACF8AC93_731A9212_573AD2ED_63A914A6_A7D1972E_C80A0A5A
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h2F5C28C8_E94F71E3,
    256'h82869108_22825900_4061B843_7D8FC251_E10C9437_7DCD6CCB_3310140E_A6E4FAA7,
    256'h831252F8_1EA04E4C_2DFF0F65_087E2DC5_A14A3105_788FD4CA_F74264A5_D4F58405,
    256'hE4631343_C184D08C_97997615_9A49ED06_D0ED779C_3246179A_D6322A1C_6DCB9BD4,
    256'h69AE4151_A1BA1054_48B06154_4001C110_48F0F7AA_C2BE12F6_36FC0D06_52DE37AB,
    256'hE996A81D_2405B4B8_47218F05_7012988E_16320447_E921DEBF_4751C3E0_676024D0,
    256'h9C8760AC_C63C7D7F_7020BB03_A8EE8486_C160D9B0_24C94CD7_B9986A82_31F7DE45,
    256'hA571C134_192256C0_28559D16_90FA8292_4E7696E0_51519016_5A239F33_B8C820EB,
    256'h4B2A4393_0E87ADDB_765E662D_28144243_00B4AA0B_82EE9189_8981CA9D_9CDF204D,
    256'h17412D80_465BA685_9B241BB1_23A7D4F9_BB81C621_D78BDA61_FAD22C87_88ADE93F,
    256'hECF42031_84EE50AE_9C7B1CE1_9A55961D_02D8928D_26F9E054_4B0210ED_C693DEF1,
    256'hB69B6CA7_5A94FA7E_31A2044B_103059F9_F1A35222_72CD139B_1885D497_DA3BF83F,
    256'hAF98EACA_4B986C56_FEE903CD_C8747951_B06BEDD5_29C0256C_C39FC301_7C294285,
    256'hC5EA852B_5734EE60_49218945_B628CD03_C507AB23_83616A50_2124ACFB_52DFB728,
    256'hC2BF5BE6_D4C7A5A9_347A403D_C8FB6E7D_22CC6BDA_42C10ACA_020D4DC4_6666A65B,
    256'hAB1AAA69_28899A5D_711D4D1B_B49F8AAC_E6F6FA31_5016F2BC_C75DA274_9B394D67,
    256'hE8FE5040_EB52150E_14A7C1BB_3B11510A_B734EB53_AC482595_49198717_4F32D6A2,
    256'h8D462A43_0E64D576_BA488F16_04B46CA0_DAC81EDC_C2050644_BFA3C0B0_0E199C0C,
    256'hD169C00D_D958CCA5_9A300686_0AA82EFB_1AAD4E56_67060384_6D9C52D3_36CD4181,
    256'h7483C359_E5597FAD_671D7C6A_C26AAE6C_BE63E37E_7C5421EB_7D9899F1_0148DDB4,
    256'h5618815E_AA5A4539_6F083177_B8DA1AC4_5A623999_4648A09E_01D29BCC_8557EC86,
    256'h06875E1F_462AF45F_6719D911_6A017AB9_42B79134_695D05A3_D7F0D52C_19CB0257,
    256'hC6512236_7B389C58_24CC366A_1838F40D_AE440A36_0E6BA9E9_14348445_9590676E,
    256'h72EA53B8_97298D92_9716D6C0_713D8CE3_28745AC8_82AEF29B_59472707_610AA560,
    256'h7A4C4A4A_DA315A10_0021A235_CF2C26CB_124EF75A_B845B125_FABB6182_A4E130AC,
    256'h14D859A7_906EC431_679599F0_CE05011C_42C50B03_5899DE2E_65977A51_D1032C77,
    256'h4DB812AC_3379A949_858285DC_7750DB55_E38C2020_F29F2B85_3438A840_E89891E5,
    256'hACDE44D5_62678101_5F0AC568_49915278_20013CE3_306DD819_48952EB2_5C6FA78A,
    256'h6683113A_AE37B564_72DE8159_2A1ECCBA_3B1886D3_FC36E188_D5393884_33E72B6A,
    256'h8B554E65_5AF082E5_2A21B96B_DF9BC5CC_B5E8A6B5_5AC6DCF0_7C7CC31E_74814FC0,
    256'h42F7482C_5E49A2A6_1A91DC89_AAFF5D94_C1D873A9_22952547_418935FC_6388AE60,
    256'h949589C7_F1317006_936AF4BC_4F1D88FC_280B6014_E8239742_2BA88089_4AF8ED1B
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h67045F6A,
    256'h5D559EF8_3E274644_E5B104AF_0E4658A0_909DA385_2CF35E3D_C04AE39D_E052BE5B,
    256'hD663299A_01B5126E_1652CB6C_5BBB31AA_B2D39C6E_B6778350_A558733E_DB9B0A91,
    256'h1752CFE9_524A0F0C_65603A8F_661DB61E_AE4DEC96_6187A2C2_F673E798_39E79F4E
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h51824483_0BFF1929_D7A956E4_4F8AECE6,
    256'h8C7B67DB_80D370D0_B61EA33F_27412CED_7317C71E_22208C29_A9A55BE7_D1D87A4D
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h2E1DBFA5,
    256'h16E8A695_B863BCD9_B680028D_E915A051_379E8D37_175707D7_713E79DA_C47A1E4A
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h00EB_0A69571A_182221A1_F481FD04_1C595B55_41894B59,
    256'hF8A0780D_808CA7A0_46647611_852BA2B6_C9280501_4B4708C2_25BC1ECD_00AB89DF,
    256'hA4936304_C00A2AB4_80719A6A_7F052428_BC63C450_D2DAD27A_26D05190_C85815F4,
    256'h21512522_A8E17370_B1080009_6B2665FB_38FD7F8F_D120CFF3_50BDCB65_714B9898,
    256'h314849AE_5B1F8DE5_1217C234_D6912632_2A687775_E2A26334_42968109_DBA29283,
    256'h4CA12053_D6D95F08_C71CD70A_4D065A98_B96B820F_9D2951D8_C9A2A3BD_2603C176,
    256'hD45A6AEA_5650A212_B40DC61D_33895E46_67C3CA18_D21D3C52_948779A5_78363167,
    256'hAA5C22C4_98196009_37C6CCF3_F6A4DA12_C38B8E8B_2BA242A0_E92FA449_9765FC0D,
    256'hD6AB142D_3F8E57C6_2B0112CC_3D938791_89F559F2_C6B1C4D6_60820361_C02416D8,
    256'hAD87153D_39A61981_9115A753_2D410AAF_BA0D2BF7_61453CC4_7300C8CA_6705CBDE,
    256'h8E4F1509_B00AEB54_F1934390_3554B45A_D4151760_950E1709_DA359C84_BD9684D9,
    256'hADE20B9C_1F3A402C_622640AD_514250BD_A6CDA0D3_715A9777_A643DE64_73EA3E81,
    256'h22104C25_8BE4BD6D_DB739BDB_DEC071EB_7DCC8A2A_496A56E6_EAF1F768_7ADC9386,
    256'h177A7924_0BAC4E63_AC20B4C5_D65D25BB_1C77D1A8_32717E79_1796AE49_3DC08764
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hBD669D5A_A715F8C2_2C0CAE76_6D53AF86_C9E6F52E_8BADBFF6_7A4569FD_595CC155,
    256'h479C106B_F2FE72FB_166A801A_04821D35_B8F01471_C8AAB10D_837B8F96_608DE589,
    256'hA5A0B765_8E3ECF90_4377CED1_6ED3F40F_265EDBEE_46E19AB3_25D423D6_DA920B19,
    256'h01D58A56_FA18E9E2_C342133B_271E942F_9F78005F_AC0533C0_09228CA8_E081D21F,
    256'h3DC6A9EA_79E4C548_F1B99320_DE5721ED_ABEC8775_CD99C72A_9B317C39_497D671C,
    256'h243062A6_584E744A_3FF34B9E_CC5DA24F_1B6FFCB2_6CA35191_5B418436_BED7B0A1,
    256'h37D8BAA4_C4851238_E7D0CB08_077E03B5_EF6168DC_DD70290E_977F2B17_FF4498BC,
    256'hE81132BB_4DB4883C_2D63EBB6_E34C6450_F9402852_02D9DF0A_95733A54_F734CA06
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h0CBA_A14D6120_265D4017_C2E03046_1DAE2F51_CCD1AD48,
    256'h7A909555_A2605089_8DB5042B_91E69822_8D92A14C_3B924663_E5590D90_15AEB266,
    256'h2C670432_38F1360C_9000BA43_D9CAEC7E_2BE7B012_FB004ACE_2081138F_5A0DAE2E,
    256'hC218B2A3_F7E81A98_068FA1A2_0881B489_190ED28A_4E60E1EA_F0B9B160_2C60EA26,
    256'h8C0CDC24_4A2F3EC7_68A68CD4_4E26B7C9_1D4B1B62_B8744E10_24EDD619_45CA3755,
    256'h412A834A_34C2748A_9977908B_311525DA_44DC3E0D_D7C34BC4_28FB0812_4009E760,
    256'h127E7E07_7F4C1F4D_556AF118_B641D98F_62CADC49_98858EB5_A2CED16D_5EF6625D,
    256'h991E0167_3D69A929_469CE8C8_10E4861B_657FDE64_D0933CFA_8094AC85_25A406E8,
    256'h84B72F5A_0AAC4CFA_258E9705_9D9C2321_04B49D88_9A3FA781_EF77A611_B20A6DD0,
    256'h9704BBA2_88D54EBB_ACCA0D07_3062577F_A6D25BE7_8545EA3D_691E4B8A_8B73596A,
    256'hE74A5059_E4A56740_A4C0A724_1C94B3A8_1442D065_AC2252B7_009C54DA_30B69D54,
    256'h22BC04B2_66C35FBE_646D75D4_6972C7A9_8041CE31_79F8AAE9_9C51E310_6AFA2C1A,
    256'h1F629E52_F6A2685D_E53287DC_58252563_CC6C694D_8E072DE0_40A164FD_5ACD8123,
    256'hFBEB85A6_7A7C1D0C_C8675819_DC844917_61745548_669F3C71_1C5C86E1_1438C26F
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hB31F6514_2EB7B8C8_6E855287_2DD58FA6
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h18755C08_04A62F9C
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h116109B0_A880BF50
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hB25FC702_912F8CAA_DB151BA7_72A8B53A,
    256'h663C80C7_760833D5_F7BE6487_ADCB69F5_944BEC50_678D3004_D4D7CF27_881ADA09
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hC66632F4_8CD4A3BF_D5C08050_AE26C65D_0EFF09B7
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hA6EAFBBA_5ACD035D_D7700FCF_1D48EBD0_513AF0C1_64B52E88_4F90F2E6_2D13A596
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h8DE63218_0FF3215B_26235F17_E73371B9_38CCC209_B5126629_C48E1AB4_5AD46B27
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h0C168892_472F5072_EE3CA90B_34EB329E_9A276322_CC738B91_ADDAA137_E6F637A6
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h9A201DCA_49D744A1_CB701702_6D90DC96_907F05BA_FD751E56_126B50AD_5C68DB4E
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hA7C03669_D35C1FBB_82FDBDD0_BC15B52B_AA0C5057_CC232895_6934A178_AB4AE3A7
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h537EEE62_64A3C067_F0AE8787_028BCC21_E3FD65CC_F384275C_13422A2D_18FB3DA8
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'hDE1F07E8_50B7F1BC_DB08CC74_4A0F36A4_28FC3CC2_481317D6_43025D14_CBACE927
  };

  // Compile-time random bits as a field entropy alternative seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeFieldEntropySeed = {
    256'h6534C3AF_D9BB6200_30B26306_197DA9B6_F314D782_FF5CAE51_7B83BBEC_D428D182
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hCC4761BA_188DD84C_87100D52_E6CE5001_95F4031A_37C17700_73400F05_C664F969
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h81684893_37293EE2_4E425434_B908AD83,
    256'hED89E532_E2C3B270_40959865_01109446_F3A0A9AF_793BD3A5_50E2C0DE_E27B296C
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hE2BBF63B_835ACC5D_A0487D9D_30E56410,
    256'h63D878E2_41CC0770_1212AFFA_2BFF92B1_0DC6E323_AFFD5194_36E00287_ACA507D0
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD167BC3F_EDFD7B45_7A929BAA_B0E7E99F
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h89FD4683_681C3AA7_D0C50C1A_09B04A37
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h1A24B6E7_A44411DE
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h853207AB_99F3EC9E_A46B63FC_4049AB5E,
    256'hFDDBC547_8397DA41_FF44A0D5_9C1D0053_0AB11A32_B78B9809_6F8670D2_DF3A28D5
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'hD4B21FCC_BB3941A9_733037B5_D2E6AE0B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h3DDCB22F_37425DFF_B914EFC9_77D542E7
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hAE6C414F_7C58CABA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hF50FB0B4_91085D97_EA696739_A6E87619,
    256'h1314280F_E8C5892B_CC20DB76_2147DCD4_BC2E54F4_57B3E378_1B32BE63_BA9E0D78
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hCF6A5979_B019877C
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h59A30EF5_73130B1C_47B66509_A3F24365
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h4FEC4BF9
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h86552A80_517D3533_5BA119D0_967D65E6_DB77609E
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h04B22181_7DD0B09F_F3FA9716_0E46DE6A
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hC27024CC_987F9028
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h0F3ABA73_5C0C0214_1374D5A9_637A5E17
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'hC58D0831_01E7C40F_2EC58930_897B6108
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h391BE560_E757B29B
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h1CDDC4B3_391ABC1C_940A30C5_A063DE2D,
    256'hCA8AC523_9F4D181D_888667A6_1025F30B_5BED6D49_EBFBB642_B3265D5F_79F98E34
  };

endpackage : top_earlgrey_rnd_cnst_pkg
