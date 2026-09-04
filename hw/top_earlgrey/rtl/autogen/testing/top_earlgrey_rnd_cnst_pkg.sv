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
    40'h23_D7BC4846
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h3867_4251E90B_69C1511D_30086018_D06673D7_0D612680_934A3158_927DB961
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h7118AF11_CDBE78D6_7060615A_20B9C074_0F07969C_CD2D10A1_A6E7988F_A528AC03
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'h008E023B_1E052DAC_1E0FCEBE_AC537EDC
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'h7848DA13_345040C2_95FCBD76_684E7170
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'h57AF0328_8E6C3C38_3A73E698_950BFAB6
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'hEA1EA059_DC5C584C_99E3E946_397824F3
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'hC0A5A56F_968FD7E9_8071EF1B_FF0C99F0
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst2 = {
    128'hC02ABD64_5FC814BC_BC1CFCFF_9F3E4CD4
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst3 = {
    128'h2214D762_08E9943A_43242540_D2120889
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'h9ACF416A_D5455D1D
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h74E7B5C1_5957663A
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV2 = {
    64'h7A827E95_A7385B32
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV3 = {
    64'hFE6728D0_D0879EC6
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [16383:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'h67BAA00A00025E7FC9BD14102DC30C29978A4C70C8DA26CB202F5F59A412A3392B9403C190120BB3,
      384'h6619E1BBA8167005EE5B59B17EF420135EB6A7B2688A16B1C05693E7E037958183C9545358D14AAED1FCF0E1EDCB0316
    }),
    704'({
      64'h6FD5443C2CB8B75A,
      256'h85CE6F2736649780ACF49BFADF4C4CEF4A487A070E2D41C244CB7240CEE69DF7,
      256'h628838F651B4B5E1188FD88EB8AEB542CC2B9D5A79CA02E338758DD6DE796804,
      128'hFBC75FA47FD1EE356B0EE77C01530CB2
    }),
    704'({
      64'h495CA878EB297504,
      128'h66316FA6C7A2CFE54B57B94CCDB5B701,
      256'h5E895532DB9EF56A3F39ACCE8428CD2F10A9BD8A9D3ADE48339BAB0E6739719D,
      256'hFC60FDA3EC7167EDF9CE31192D35CFE634069D6201333F656283E5A7BD289D1E
    }),
    320'({
      64'h8A8E59E8CC6315D2,
      128'hAD9874386DBD4C92E0F24A7DB2A9D1F7,
      128'hAF22D4755CDDD7CB28EF0FF7219351C5
    }),
    128'({
      64'h2CB21F6ABCDC9A60,
      40'h0, // unallocated space
      8'h69,
      8'h69,
      8'h69
    }),
    576'({
      64'h12107E5F93709238,
      256'hA302E95EC6D2AADEA8B6A9D4477ECD98A528E88DD62172CAFE980B4C39261457,
      256'hE17E956C21B003D0BCB1CBCD1EB02317A6BC237A3081D9BCDD43BA90DE4CF7E1
    }),
    320'({
      64'h44E91725013B44B5,
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
      64'h171184A5B1C2CBB2,
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
    5440'({
      64'hA1832965B9E9EB47,
      96'h0, // unallocated space
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
      64'hE7DAA2EA63EA3209,
      64'h0, // unallocated space
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
      1728'h0
    }),
    512'({
      64'h18A937E66A6DF253,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h2E0A6138_CB8316FF_95C65CD7_A1A768B0
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h6E0106D6_0EDA0F1B_C67ADF85_BD9A56EA
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h088D33FF_AA6A1155_AFB0169A_B2DE3973
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hD027EE30_B8F901F6_44EC7CD3_E56C8ED1
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hEC38739F_1D0DEB7C_774199CF_6DD057F4
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h4C13E25C_7A5877BC_5242E6EE_63ECDF45_8AE6596E_87F9F973_DB98AAA2_93568FD1,
    256'hF31A0165_939D819D_1518690E_6473CDB2_47939163_5057CA10_45B9E191_7E1FF018,
    256'h9B04A4F7_FBA960FE_098A4FB9_D469171B_950E364B_0DAC5469_568E6614_98FD8919,
    256'h7CCAE8EA_08FF43EF_C2BFB1C6_AB5CC63E_6F4741E8_0F777CB7_FC05041A_1B896350
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hC9636D68
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hFFA381BB_81920D7E_B1ED8254_0A5AB99E_C8B29F42
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hE083CCDD_BD2A1B00_8057C22C_884ED49D
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h87A5B56B_A7353C53_2142F506_67E220C5
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hB724C3FD_B6D06065
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hFC273560_35AB2219_1AB89F1E_99536867,
    256'hAA5FF65B_C1C4A5E3_F92E111F_2CCB3F0E_401B6EE7_DC432C15_44E0D1DB_626EA40E
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h25910840_042A75EC_C25D4E22_67E3BFF2
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h6E003AAC_BF7D513A_EA01E9EE_420D5B52
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h3F6B00C8_1BDED728_2425B1BB_59B80148_1ED5793A_CCFB3AF8_84AE3784_05DBCB55,
    256'h08CD6CD2_CE715E7C_CEB1BC1C_61B3D27B_B8E8398E_880ECD25_2956BA81_616362B2
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h7EAFB903_EC79BDDF
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'hAC72158D_4725E3A8_7DE5BB9E_38AC9D31,
    256'h142DFD2A_B5C3436F_5976991B_3A4F127B_2683B262_14B031A3_E0E4637F_3605F4C2
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h4A617569_CEFC9183
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hBEACE328_B5B611EE_1960EE81_FE9989C9,
    256'h51A7339B_6042877E_20537BC3_C1C200F4_A2BA195A_B3191353_445BD5FA_FD5C3737
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h4D9E9EB1_1CF8D3FA_0FF96264_5F7C9A6E,
    256'h120E13D0_309DDD52_BDC060F0_5AB12CDB_47DB9882_96352956_B61F2900_EE1A6ECC
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h47A05221,
    256'hA8D0F96E_FBEEF3F9_FF6B5876_7302C229_957B7D15_9740CA72_CE50C559_20BA14E1
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h90554E7F_0F8E0C0A_84694608_65342A27_1F796B99_873B2E67_8040824C_6606001E,
    256'h256F7483_424A6E05_63205672_8F16366D_9F506837_21138B1C_9739852C_644F2395,
    256'h70916224_2F047A5D_579D9A35_17482941_453C7644_3F9B5E9C_33967873_328A6094,
    256'h02183151_752B1B86_5C0B889E_61595419_017B2881_980D471A_07114D58_6A12095F,
    256'h8D2D1015_5A22937C_306C3A92_8C14533E_434B8938_7D77523D_0E495B7E_71031D26
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h57900010,
    256'h3032EED9_00BB073D_9519792F_AECDF667_77FEED15_0DA5FC2E_CF4C99C2_FE249B87
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h719BD589_B581B1E1,
    256'h9629B258_35BC7A89_705286DF_2ADC250A_2C8BE0E9_4A01855F_FBF90489_1E869A7A,
    256'h705BF0F6_C7AA6747_AC047EA5_F015DF40_8D7240E8_4DAED682_73615F56_5C61328C,
    256'hF6722324_E5E4F80F_31AA38B6_FAC460A4_79E5B169_26BDA75E_89F3D4AF_18EE9A14,
    256'hDAA7AC27_1F023069_739D0E0F_E137C8B9_0DE91B9F_125D6A63_169D7922_A3DEC36C,
    256'hAC4651C8_10800B4D_901C8970_BC8C389E_C5BA4545_58F8D626_64E90B88_3296AB3B,
    256'h3DB80390_847E64A2_E3654E1F_3A441B35_31A70197_C7002F1D_B7F23705_CEF0C113,
    256'h4D633429_1A179101_51674E8C_3599CB9E_2AB8690F_9B18B176_D5264A09_CA095427,
    256'hE799EA49_60DB8E8C_41A1C341_2E4AD9B5_6DF828C8_45E2BC1E_61BB2A6A_2C533255,
    256'hE001AB66_582A514F_62EAB1A5_60010E22_965E1B65_2A6201D5_60F02D4E_6539AA77,
    256'h89116D64_21DA54E1_563B9195_4A409FE8_A359F40E_EA75D8EA_B4452739_65957161,
    256'hF6B91D54_D8C45829_07015C48_A630C5A0_DC0DA4EB_38683248_E6182E4F_2998F984,
    256'h9AE46811_9D5C2059_9EF494CC_00D5CD11_8E00713D_39289ADD_AC2E2F66_244C8590,
    256'h0A3853B5_923630C8_7EC330A1_DA99AAE1_696193C6_22F9161A_834BC894_91C45C4D,
    256'h9F845218_52A14BEE_1450F27D_C9636154_1D0E3295_7E49CCB2_9C9CAA21_80B260A0,
    256'h450094AA_462DA0AD_32BF08F8_EA702DAA_2346AC82_2A431EC0_AF6B507E_6FBAEBE3,
    256'hE86D0795_96291BA3_50D82D82_656F81CD_CC13C8B1_B8266DC8_14C318C0_5DD9727D,
    256'hB3071A7E_A07BDD27_286F13AE_C935C505_9B11D898_5DE197FA_4CC74D90_B5694B44,
    256'hA0806618_20F3F2CB_3CDD81AE_49190131_54B38F2F_7B415F55_D0598ED4_7D8A8BE5,
    256'hA473D743_AE394B04_B34CB2C2_684AD0BD_C54882ED_7389C927_E50C1460_374529BD,
    256'h71BA3EFB_4459920C_ACBBB17C_1E5B959C_375D5581_CFF52EEF_374F15FE_3F686870,
    256'h5232A506_77CE28B5_F1FBF563_482793FA_21A2011A_6C5F3EE8_37501AB9_8238313F,
    256'h0E0D28B8_CD28B148_497D26DB_C5E70F13_49E4ECEC_C1141B6C_F95B47B9_618DB782,
    256'h9C395E5E_E62B054A_87449502_96678C44_718E9F05_9B708D92_DE31B171_A030861C,
    256'h0C4A009B_49220F12_6268DE8D_15A3515C_B95D32A5_B0512BFA_6A717C09_D921EE04,
    256'hAF091303_8ECAE02A_5D394159_EF1C9B9B_9405C404_044945FD_1014CB20_8053EE49,
    256'hB5124256_A51E76A9_4F82DC27_1F87F6A0_56576425_B1A9BCE5_4091A36E_D244E710,
    256'hB75D6B80_8A06E612_FC076B9A_D22422BF_E3D7A5DC_0C537BA0_3E33AF12_B5073871,
    256'hA6CC03C1_A93AC2BA_47580009_D98AC017_88A6AB64_32180D06_257085E7_BAB0B9A1,
    256'h469A5721_E2BB85D1_7ACAAA1F_1432143A_3F5A2330_5C64A026_4581C640_8841BAA0,
    256'hB0DA1AC6_40D98668_829DD7C5_AE308E1A_B6F8D575_43911CDF_52560ABD_346D2509,
    256'h28F49955_12C1ED87_8693B50B_700DB1DD_D0C2948A_E220309B_6906752D_2D802DC9
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h1A8447BF,
    256'h83B69C50_E149CF51_784A9D7A_C691306E_5C56CE38_CD7D7E3B_1ABFB797_8189A21A,
    256'hE856F1D9_08E3F70D_E343D222_6E9E8644_65A8EE55_EC0E6A29_6789DED5_C0AF59EE,
    256'h62F1FD1B_BEBEAC22_05B1FA5E_94E72EB7_EB1A713A_D15D2565_D9AB4FBC_D2E17C40
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h3FEF769D_DACBCB3D_5880922D_AA3704A0,
    256'hD1595ECF_0EB8C7FA_DC11A992_15BB9710_13E03442_BE67B057_9FCA51A8_8743449B
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hBD6684A1,
    256'hD596CC57_E137A032_1FB803BF_D2DE7A90_A1357E74_3CE46044_2C10686E_82613DE0
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h07BF97AA_91005905_135084ED_BB6BC55C_92B2AF81_28480F10_444B7D9D_5E57CFB4,
    256'h47192CB5_1F3F5517_1AF8F020_259608A8_783C567A_266FE793_14160C3B_6675C0FC,
    256'h9AFD4618_AED8E3C6_7B1B9B34_E5CC79C9_DDFB3083_C1452B3D_FEA3889C_36BA9F4A,
    256'hCEA040DF_E8C86C67_43D986D3_A6EB4F87_1C7CE0F3_728F94B7_6A230BA7_8CDB733E,
    256'h0A7449B8_EF6E1277_F7315352_CB8AE9BD_42F96829_98951EC3_71382106_EC0204B3,
    256'h27E4F6D6_8B7F54EA_8EB1D0B0_63BC4E5F_E23A6576_A50E038D_379E4CF5_CD5B4185,
    256'hC2FF995A_AC70C424_B9BE6915_2FA13351_2A2EF2D2_D1AB0DA4_E1F1FA64_C7CA115D,
    256'h3932B6A9_E6A29058_09D4DC01_D589624D_2DD7DA22_82F47EEE_6061AD35_1DDE6D80
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hA8413DDA_43FECDD6_C1A58693_232D1C3E
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h361D856A_B2D1DC64
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h55D87F13_C9A46714
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h9B9800F5_F3B215B5_A820FC44_2C793FE0,
    256'hC8FC1909_D94F6743_CC129895_EFAB84D6_BB2578B7_D2E7300A_952CE92B_7556ABD1
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h8B1222EC_6A83A5DC_6907A83F_9BCEC15F_3CD33E84
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h447BAA83_C3FC818B_B3B4A840_AD3214CE_B3F354CA_2E089302_C3EE1D69_5AA61628
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h3205DB05_CD6C1888_8AD01FE0_46EAFD8B_F298DB7D_5FE0FD32_A29689A0_C1549C28
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hC210C01F_F7E6E6D2_0E0404E7_B51D020A_A3695DF4_2597CACA_EA4E16EF_75A4823E
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hE1BF100B_50C3A2C1_BA79A60B_D0D947C2_6D8D3C38_74C6B8E3_4A85925C_E73B8F15
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h50985EB5_03E8E407_13152D13_2E9E94DA_720A712D_7D6B7326_F3102BA5_7AB12F0C
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h11E464E6_13088D6D_F2CC4352_AA62DF6B_07199EA6_C6782AD9_BB2E78FA_04C68991
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'hDE3B57A9_B61206E6_C0A2AFA6_A3C56D97_128C7811_E36A2829_DB025EC6_95470623
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h45C400F5_EF1B06A1_19650A85_C3023753_6DC3E350_40DE9AC1_A6F2B35C_99FB71E1
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hAAAB3C20_8383ADF5_0311FF71_FD469219,
    256'h23A8CD8C_6FF98F9B_DFC2B205_D8690DD3_5500E5A5_1BBA34A7_1D81E9EB_876B6F19
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h96B2BE4B_58DFCFB8_30B9E25B_DAA3E1AF,
    256'hFA91806D_01A89BDF_5084C3F0_43FE74B4_FF850B4A_6DEA9777_4B63EF1E_13CA69B8
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hBB7DAE31_57B7279A_2BD0F451_78ADD409
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h9B463A9B_FADEB0A2_49E67A25_FEEA95E5
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h0B27DEDC_6815C375
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h4DF7B75B_5AD13CA3_4E2D9074_BBFCC363,
    256'hEE601288_C0309C87_19C9F1E1_05240A29_7BAA6229_5576ECF4_5776C1AF_12EA1BED
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h1C4049D9_B85F9DC3_C99A3786_8579B46A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h84095EA9_81140FF7_F0C4AD73_D5972677
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'h4A37E335_60266D52
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h88755A30_10E0B1D2_BEBC2A7D_87A9917B,
    256'h8B72363B_884FFACF_27566A50_5425CD75_9CD376FB_F0B7C6E4_E0129F06_04931DA8
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hF5AA54A3_F54824B5
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hC6538F8A_AE68EC24_DF2D9B07_0658CB5B
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h072BB74E
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hE183A239_7196275B_B4451D92_ACB3DD01_E08FD36F
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'hD474657B_77F7EDA1_A07047F9_37051A05
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h7461414B_8B3587C6
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'hDE71B922_084EC4EA_31A97E0A_CB1ACB48
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'hCBA01DEA_88816DC0_357C3D41_9213EEBD
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h8FED49C1_67447D0A
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h479B3C90_405BF728_3A1EB57B_A685852A,
    256'h54F509A3_463CB499_73726F0E_377FE21D_A68B360E_AB17B001_07D7B6E9_F4314F88
  };

endpackage : top_earlgrey_rnd_cnst_pkg
