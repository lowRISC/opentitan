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
    40'hCC_8B20BED7
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h95B9_1739D7C8_2E378688_A9D08493_C01E6060_64314D50_24D84551_0C59C692
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hA7D4F4D7_F99B4A64_80DA2D53_E7CA1520_1A8F5653_0010117F_58C9E994_6C111804
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
    128'h07FEB471_0F404E6E_4FACE59B_972D1FDC
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hAF711C05_69397BFC_41976AC8_6B02BF2B
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h89BE218E_CED8859F_464D1D91_0540EEC6
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hBA0486F0_7CFFAF7B_8B9213BD_8DC7B927
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h797C09DF_EAF1272B_92ABC409_056CFA51
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h3AED0DE2_186C2B2A_4874E4AD_ACA4C680_9E571B35_1756BF8D_18E24BE7_E1C96737,
    256'hB726A4C6_F04993B3_E6AAE70F_22AAF748_B57C3202_64E157E2_C74A2803_3261EE6C,
    256'hEC10075C_55A820F8_42D43EE1_AB1B3D78_F992D223_469898EB_2AFE18DE_121F1E16,
    256'h4EAC2904_2563AE47_33313AD2_696788A8_735B2798_2F5007A2_4A125F87_6C9CA6DD
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hEB52AC92
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hA4ED170B_43E265F0_41E6267A_DC1EAA5E_EE82859E
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hAB227B50_766D2EAE_C89EB13B_07E9BF4E
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'hE4278413_6D42C85E_456F3B26_D15F5584
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hBB9879BD_2497852C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h3DAE9688_B72646DE_582546D0_3AB7FEB2,
    256'h9036A21F_32C45564_FEE763C3_B7990AAF_4683712F_0571C397_8D533734_8C9CAD08
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h9611E658_C97FB8D3_E9CC0E7F_8FA87252
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h00C726C8_F90EF5E2_B74BEEE2_7CFA19EA
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h576CA8A8_225C8E17_053E44B6_8DD7822A_6859F2CF_52A55FD1_81B082D0_3C583756,
    256'hF11AA5B3_7F9544C4_AA90EB97_E1C0F808_6F627A28_1C5681D6_566641EE_CCCC8887
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h6AD113C5_0AD1BE4D
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h9D31C8CD_498C0C03_A2D4BF95_8EAB5E12,
    256'h06C1F78D_B9EDC92B_35D14625_A7D6FEC6_70C7C611_5F2BAF3D_2D028682_90A7ADE5
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h79B106A8_7E59E6AE
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hDF402089_D216BF2D_597B89E1_5473CD53,
    256'h10D21BBE_5A2BF5C1_8F362AC0_E7D3902E_A9A11AFC_6E6DAEFA_51497044_3D2CCB6C
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h8A82AC94_503CE485_F2D14931_320D96E1,
    256'hE4B308F6_7D68661B_983BC79F_005CA5F8_53FAEDD0_8CEAEA25_15752FFE_CD13AB5D
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h7EFDE3DE,
    256'h5B4CAF47_76A247BA_BA4C9908_ED16BC54_15EC16D2_8C535513_12FCEDCF_2832A66C
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h5E7B1B21_046A3130_2E681006_845A5B60_96431D7E_35440E4A_27376678_892A3F76,
    256'h28058B29_22476186_1C9D238A_1E8F9041_574D9C07_987C4F36_46000F99_332C2403,
    256'h3E7A5D01_0C7F0A87_02091358_6739829E_77694938_0B9A1897_592F9408_1A326B2D,
    256'h4C197080_26955554_852B3D0D_645F9B11_25125091_4542408D_159F9272_6288833C,
    256'h5C742079_6E8C6D34_4B146C51_6F3A7173_52486393_8165531F_4E75563B_7D17168E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hF0B8CD9E,
    256'h17606EC9_81060E94_795A1D57_3089578C_104A36A6_47E90FFA_FF9760F5_E838BD8E
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h4299C078_D88D2FAA,
    256'h5D2E0DA9_945D9D33_05327800_9BD8C02E_EDC0C0A4_94A65CAF_76022BA2_87D05C8C,
    256'h5E4D1850_682DCD28_BADBBD6A_2AC87BB7_71A23854_8D5FCA6E_5C87E1A7_26853507,
    256'h02964526_56FB427E_48EA1B26_052B8B9A_4813AB04_6482DEA0_D7C2B098_7583E796,
    256'h8C4D0625_1CC70AE9_1B49F54D_D9584443_4343D2C8_F83A0A09_31C6C4AF_829C6C46,
    256'h44D83C6F_4D4D93F0_45C757A7_B2687A71_520EFC5B_940B6284_64880252_61A1DEFA,
    256'h26E10BC7_66FEC859_54DB1250_77DCD9BA_403B6943_F489792C_27A16D39_55D892C1,
    256'h72072782_362CC107_99616F12_B0E1C512_27A46EFF_C7D01148_6D8C2037_4E9D3D87,
    256'h7739B162_31CB29A1_4B1D76D6_5D2126CC_00792154_34849A59_8C3AF8FE_63ACB101,
    256'h14A43176_4CEC6243_47F56926_D73579AF_C1248B38_F971E39B_DAFB78AB_D068CE93,
    256'hB065E030_72E63045_36016BA1_291D9441_9616AB55_AAA17D9B_8E8A242E_608C9EBC,
    256'h05586997_0A19F01D_53F5284F_4F2EA61C_964B6626_0487AEC0_38CE65A4_ED5A9F0C,
    256'hB68372A8_1B47CDF1_1D579510_75ECE3A0_2F164015_C2DC3007_0F8592A5_52F23C22,
    256'hF56EE3B3_6137BA8F_8A93D039_EA469523_266AB00F_57F9AE76_0E2391FF_8125B09A,
    256'h436AA3F9_C924978E_9A22A57B_6B05B258_081F43AE_EE12E71C_0A180241_C4E3099D,
    256'h4BF2343F_45431A08_2C8C43A6_FA0A8B1F_90A55A54_18D40D55_221595DF_08BC14FA,
    256'hA310AB51_CB3D6080_1AB2E313_1B942160_215FCAB0_B5C1510B_41FDD59F_28E18609,
    256'h4C414B94_C0A0508B_66B7691B_32F6645D_99F8414E_59097AD5_7D0A1480_9DB08F5A,
    256'h38F03B1F_05A499DA_6B5B4209_3B380029_48C4B725_7666C318_09C3DDA7_652770B8,
    256'h35532A65_D4EE3E90_6BFAC517_0F34BC44_246708A0_59831D12_C065145C_0C461B18,
    256'hEEC5A30D_8A5D2340_BC410D68_85165FA5_9BBD0036_93315D29_4E6E9399_CC176E67,
    256'hCE499363_87724252_4562ED09_61A5F1E9_6BA60868_709D7E95_1248EA88_13A035D9,
    256'hB5E464CB_1EAE2178_096AC289_3154CFB7_CCAB3025_628B5822_BF60EE46_DD849A44,
    256'h1959D035_69F37B19_66A78314_07228188_FA962FAE_B0F0AD77_8DD2A012_1AE4A58A,
    256'h5AAA5454_41A5286F_91F9BD7C_53E25695_2EA5305A_BCBA19E6_A196865B_A08E8B9C,
    256'hDF8A90C1_B820E478_6A03E557_12660899_79F53088_C9F8881D_ACCF2191_53775A03,
    256'hD0C61E18_F28E0643_1A919AB6_9050260A_E2C1E760_2227A72F_D89AE738_62D7DCC8,
    256'h3360D9E6_7BB50DB4_610EA680_648873B1_EB1B59FB_750FBC50_81A824B3_C5B9414B,
    256'h119E0762_ED3896AF_178C278C_3335F188_2C71A794_19D0495D_0AF0AA6D_8DD67A8D,
    256'hDB5C5F6B_180C849F_21A44216_CB6AD0A9_78705AE5_A21D21E4_9E47B471_B34E3B23,
    256'hCEF99C04_4A21D142_6BC584CB_D2F379E8_D3FC2432_F0E52E4F_72911519_CF9FD0F4,
    256'h495C8051_3708326E_E443708B_6DA1558D_910E4E72_91986E15_F07C4E6C_9ACAB890
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h8CF20CCA,
    256'hAA3BD0E4_E02590E0_9C975C71_CA965F7B_316D6C12_EA819870_D451DC29_EE296DA1,
    256'h850BE6BE_D073F6EE_870F58B8_9FABFE08_C827837C_7867EEC5_8FF573DB_5AAF6E95,
    256'h644DFAD4_262A7ADB_7F05D963_E4282AE9_DDB8FBE7_A138D956_AC336341_A536F70C
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h9DA15FCD_48A3592E_C8C412F9_3916F5F6,
    256'h0FB4FC67_66013610_B2536AE0_CDEE1EFA_29559282_C2478973_65ED8721_3CAC3E8F
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hBF228C9D,
    256'hA633B0A6_09DA1E36_7D6DCF89_E31E398F_A71326E7_7156C7F9_F68F1022_98AB6A1D
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h1803_2D9C1CC5_00411BE4_0990464F_474F50F0_85450AD4,
    256'h70D49137_11EB6043_00FED965_5CE6B177_63AA0F50_491CD765_936B1967_2B323416,
    256'h93A8A885_A45B2FB4_D7EDE960_36CC8753_30A3F0F3_E5A2FC6C_0D251F93_CAF09C13,
    256'h0675C026_08C4DD71_AC0555D8_2F203918_98D66726_88DC0995_8DAD985A_7440C68F,
    256'hF470F597_4C222B06_77A9C2EA_315F619B_D555A1D9_29FAF7B1_0AE54865_BC507C5D,
    256'hAB941E80_21458CCD_6D5E8299_E06084D9_60451756_4E0E7A53_5C0F40AE_D46EA719,
    256'h75F1CA52_30881111_A732403F_7B6ED2D5_25149851_911B63B3_6184E46A_72AB282B,
    256'h1E964F35_F15E4876_40005130_D20AA29E_ED845268_8DA195D0_5AAE4531_30521A93,
    256'hE8F62409_05C8D58B_2362FB4E_B78DB073_D5220D70_42A98612_2396091C_9F110250,
    256'hA20726D8_55F0625E_12ED2F02_18FCF134_1B86E3A3_C51A9EFE_0CB94EDF_C4C854FD,
    256'hC2E97B50_5723045B_C8AA69A2_8EA62299_3210F25E_9783C387_417ABEEF_6C374DD0,
    256'h516C0A54_C031689D_4B8988CC_066685AB_268D512A_6D223920_AA0AA264_9B73BA5A,
    256'h971AB261_D2971A88_4AE24B58_4D16A0F4_153A0B0B_282ED099_F1DDDE53_BC5C2B68,
    256'h178B38FC_F50C921A_A13B888A_04AD9CD1_A4A7D7DB_E54A1D72_47ACA584_FC2C5863
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hBD02D6D0_7BE8EACB_5D7D2E8D_056D8C9F_7ECE6BA2_A4AD06C9_E2D54DB5_35BF9C65,
    256'h0CF1FAC5_A648F252_8B414C10_4084A75A_1633BBAE_C62C54EF_E312E4F8_1C93E9E5,
    256'h6EE1F083_72365F1D_850D8A1A_01FFAA77_0024099E_F7C78F17_37A1A532_D190313F,
    256'h82579508_4F0AE02B_03669164_8729B3A3_2FD86270_6F9439DE_DA11F423_4EF66C4B,
    256'h741E19BC_1388B1FE_BE760B21_73CF5EFB_464ACC68_75E7DCFD_635B5CA0_FCB867DD,
    256'hC438BAAC_28797189_0E7A80B7_3C3B476A_9634C051_EE609AB9_8EC10714_271B5961,
    256'h4442F3CD_DB2A7FE6_DF9BCA92_563EA926_3DD21804_8645D9B6_B4229830_8197D450,
    256'h58B0D73A_202543EC_D3559953_A878F91F_F52DAB15_69EB7C49_C20FED9D_B2C3AFC8
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h0AD8_E33F0123_44276A40_C5792874_BB13DEAA_C908259A,
    256'hBA1B88DD_5DF836F8_50695504_CB5501F0_D02C6461_4D3F2349_E9FBCAC6_DE5A8FC5,
    256'hC0E86B1D_ED2062CA_DC28D613_056F5080_3EE71399_D8D97A10_8C835CE5_D0BE0462,
    256'h182726C0_D5FB4214_EA037584_88660B7C_F63A3728_1E2188A3_E1DA8C2C_C12FDEF4,
    256'h089930CA_D622D94D_EE524398_10691D99_14E42123_31FCCD19_8112F108_C1ED622B,
    256'h87426B17_EA2C0A4A_D871B647_09287D72_B4212ABD_1728FAF2_105A7759_1FA64833,
    256'h9D326AD2_13256F25_3011CA97_2A3D3282_2B01E406_F969102D_A94FA94B_8A616246,
    256'h1C0CC5C0_B1C45E91_2D028726_D7648A2C_05353BAA_6D7119D2_166C4A34_E0B43A10,
    256'hA052F82C_102FF077_4DD89A46_725C800B_4512069C_9F1151CA_E512C81E_157B208D,
    256'h5BB413EC_F2CE2A49_B5493787_EAF9431E_634CC96E_8972AEEE_A6B84A2D_D59B553D,
    256'h31492FA1_8C5373CD_6E36A318_30C3CD19_7C9CC69C_27DCD488_954ACC8F_6B5D5855,
    256'hC1C5E1FD_E71565CF_9DA3D43E_12E3065C_22D80A54_CB1104A0_934D0A81_5702A81E,
    256'h252F550A_56DA6CB1_A8F02242_2246778A_B1F21DAB_B6A6256B_25F47CFF_6486690D,
    256'hB8A4E9EB_17BA372D_86B67582_428E09D1_26C68374_923E0140_40EA25B6_8259D4C8
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hB30CD2C8_013E71D4_DDC47808_8F7515C4
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hD1C787D6_9CF21F70
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hB63F2877_9E797D82
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h5124CC8F_020AF367_D8137251_5B5A7ABB,
    256'hFCAB08F7_45C41F83_B5EB0602_665ABE15_E51F4CCB_43B72739_5A3889B3_6AF79920
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hD4788ECF_14DD6EA3_8D39787D_2596CCF9_1C011A0D
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hB55AB7BE_362D4DAC_19F54413_3B97793D_3B4C353A_8DF29F38_E6A176F8_69052458
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h0F711F01_7190E3ED_05C573C9_AA17B2BA_F8C063E8_EB49C269_574C9DB5_81DC4F66
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hC2C27FFC_2B8538F5_39BFF9A9_50AA7944_B18FB6B7_6A1F5B19_08205A32_959FDFB3
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h0BE24EBC_A241CED0_AF4217E0_1A53F2BE_7FCBE757_80DADEC2_B1FA0110_731127A1
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h203A94FA_13D41E24_35278BB8_C68210D7_3CDB0FB6_651C2B1A_6B5BF1F8_3C73FB08
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hE172A7C8_5EE09EEF_847866FE_33518FFB_B881946D_B7319EC4_0FB2D8DE_353CF8AD
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h74C66D60_D2F5F466_E8ED1AFB_0E2242C0_5CE59E25_589D988F_6A009A41_C3ADA4B6
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h638D11C5_22F5567A_C7CF280B_9CD698B6,
    256'h9BA2DDE5_44D44B57_B9F70DC7_1CEBE056_83E27594_5DD3DB22_3C4CE721_7B90B94E
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h354E9BA1_F613995E_87DB8DD9_443DBC2F,
    256'hA7345F78_4B982902_E3D24053_88C4BDF5_EBF9AFF6_D30A8FCD_52677DF9_D787CF38
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h07946824_D2F97B69_00CAB42D_E4AADB22
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h48723232_922A7B25_AB26360F_6052DAF7
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hEFE37406_1FBBE322
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h89D34F0D_F12D2E54_64339B05_9C61FF53,
    256'h5DE1BC90_68B97232_D9EF7B82_A67CEB8D_266BEAD3_0905A973_148A6CE5_408F3630
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h3B9C9B96_1A1B600C_24D9FE64_0FC7410A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'hE219881F_4EB78870_E59D2519_91A4F774
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'h8E9EA5B7_D587AB0F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h2D455FCD_D4859879_1E8BA26E_859FA98C,
    256'h3F2DDF53_82B30948_9D172F2B_44E8C8FA_B8006416_E4DF76AF_BFD86E06_B15CC044
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h41355E03_F33B67D9
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h598B6A8E_2C96563D_30044F29_11352FA8
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h650C99F1
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h525162CE_44C8F660_AFB779F0_28D3FEE5_40C83B4D
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h834B1156_39A3BB54_E2C5F80F_764C69C2
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hDBD16CCD_2B68A777
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h2BE292F0_27121F21_E3C1230E_C2C7EB42
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'h462784A8_23B2ABFB_D7F23895_4AF41753
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h4BDCBC61_8A44DD79
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h5F1D2F23_BA11D467_8EF8BFD0_1568E462,
    256'hECCD3DC3_141DF489_999A7C74_0F60C83C_139E295A_281ADBDF_9B3AAAD5_781360A1
  };

endpackage : top_earlgrey_rnd_cnst_pkg
