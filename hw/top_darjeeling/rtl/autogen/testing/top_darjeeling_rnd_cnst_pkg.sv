// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
//                -o hw/top_darjeeling/
//
// File is generated based on the following seed configuration:
//   hw/top_darjeeling/data/top_darjeeling_seed.testing.hjson


package top_darjeeling_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hEB_A4D1F0AA
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h1602_C23D095A_54E5DC29_19044C01_9D6C70CD_65E85F20_98E70568_A6512318
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h2762E7AF_02FAD0A0_B00419DF_7239BC95_AFB3198C_AAE47DE9_BB857ED5_48272082
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'h688A9A20_B68E0D35_660E593F_560F6866
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'hA1AD90A5_09423977_40AB78C5_737A2379
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'hC2EDE5B2_5EC5514B_680CCAAB_361C3F85
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey3 = {
    128'h8E1C5CCC_C121A2C9_5D21294D_190AB75C
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'h09C87E42_745452D8_A010A9F0_EF3221D5
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'h4DCBA329_FF2F7D4B_8A3ACDB3_25087FAB
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'hA0806E02_A1FBA55B
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h9BD623E4_0AEC9B61
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [131071:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'hD08F694A5F790581D728BD369D03F8087A60A7F8ED956442C9CFF0F99E594C7307F376E7B2B2FF8C,
      384'h6149B9FF4F5979607AEAD63A44F896431DF745A52C5AF5FDF86D2CE9FA1041C43F145A8BF5BE7640D7AAF2481067180F
    }),
    384'({
      64'h0,
      64'hBA37DEB973D827E0,
      256'h9C47222C695C123916E90F1BDDE834C31D3EEF689E998822EDDEB20732F666FA
    }),
    1024'({
      64'h0,
      64'h5A7F3E2373A78AA2,
      256'h276D9C42B4B5C6539C73A2705A4682BAA1885457797963C3980BFF063FC8BC64,
      256'h2E2904AA8A7090712CF9A372BE9C2B9C1FBFF3B68368C5AFEDCDEE44F5D8D84,
      256'h4C8FD64171EDB20835AEF32CF20B0C620E9AF6C53593DAEC8E3CAA2E495A8976,
      128'hEFF32B59C0A86294D9767FDCB4745699
    }),
    256'({
      64'h0,
      64'h8688686A7D26F94A,
      128'h2552A6AA7830346413591B15ED255318
    }),
    384'({
      64'h0,
      64'hDDF650F1A00008EE,
      128'hB5742826D2CE8D8BB874DDD1DBCA5322,
      128'h1FB5110B0618183CBF722F142EF9FACF
    }),
    128'({
      64'h1F2A6BD606D55F72,
      16'h0, // unallocated space
      8'h69,
      8'h69,
      32'h0
    }),
    576'({
      64'h6FB88C3B4FD535BD,
      256'hE78E601C1704C34A6DFD043E96E1EF76D15C0798EF406091D605165216FD3F85,
      256'h58B183F3D37975B4A9524DE21084A9D64BBA835C10B5E29043022273F7AFBF68
    }),
    78848'({
      64'hCA832DA13EB53FEA,
      5248'h0, // unallocated space
      73536'h0
    }),
    8192'({
      8192'h0
    }),
    2624'({
      64'h28B1AE331BF3824C,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hEBAA1ACD79D438BB,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'h8A4FE08CE276C9C9,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hB5A6FD9823EB9F1C,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hB51350C5C23EBE77,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hFDEEF22E74536D01,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'h4BEDD6920E68A84C,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hF9D303313B0977A8,
      1280'h0,
      1280'h0
    }),
    11392'({
      64'hC167C84BFDB86457,
      32'h0, // unallocated space
      6144'h0,
      1280'h0,
      1280'h0,
      1280'h0,
      32'h0,
      1280'h0
    }),
    384'({
      128'h0,
      128'h0,
      128'h0
    }),
    4800'({
      64'h2A24E15352C559FD,
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
      224'h0,
      3360'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    2496'({
      64'h9521702FCBCF4F54,
      32'h0, // unallocated space
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
      64'h0,
      32'h0,
      64'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      992'h0
    }),
    512'({
      64'h45515694E825B33,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h722A788A_2FA6D507_84BD3B82_D9D4653D
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hE5A5288E_14D20D64_D95E54C5_B57D5FE6
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h1F96E6C5_40D47A3C_4757EC8A_8986B08F
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hCB77D083_1159F325_0B813449_C66DCBB0
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h21F7A92C_F5C0C6AE_053B9955_62D7FCAF
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h6DDCA620_03655CEB_43F3E842_F268FBE2_6BDA6F7F_B2D7F5C5_A0BC44A9_AE1E094D,
    256'h11EB4CE4_297A9B8E_A751D573_0C85237A_B633C270_80416FBC_BCA04BC1_FE5D4087,
    256'hC45F755D_6824EC5D_5E48742D_D52E434B_64D69E2E_2FF6AD2C_726FF1AE_C6468A27,
    256'hE6FBA320_3934135D_0EEC1A87_69C1E22F_FBC6D0CE_E9597BAF_791F6ED7_367FF7E8
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h869207ED
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hE35C612F_C8AFE44B_654C8530_97867DD9_4F1BE860
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h0792B7DA_71DD3E63_D444A8F8_D3187278
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h8BC872F9_B8034717_7C4A9A3F_840B2F50
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hCB196701_842511EA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h17D9DF4E_BBAA6827_15BFA6FF_E76934DD,
    256'h846500F5_FC762506_D4405022_9B5E2E13_3098E5A0_663CB32B_8B3E3432_684BB1F1
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h2CC5A50B_94886C60
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h5938C856_B6011467_34351F69_89AB7BDE,
    256'hC6CB4BC8_7992FCFF_A9799903_03830BA2_719F529E_31FDA5A2_EF944388_0774F132
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h027C6C22_DE24F6AD_6589417E_EB71CD9A,
    256'hE66BEE3D_3F45FD9C_32119B49_D54ABE00_F9C8F381_C28CD76A_92C443C4_C909859E
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hCCC4B270,
    256'hA9C0DFD4_ABD37BCD_E2CFC891_E919BD3F_ED814528_A693BFA5_292F2DFC_CEDB7CCD
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h4820621C_8F251864_833B9682_1E310E0C_608A9B7E_306A3F5B_4B17636B_53163651,
    256'h2977276C_695F0947_459F210F_37703D1B_92545839_035C7F66_10002D15_193C4C4D,
    256'h02569922_0D862C2B_069C5543_72440A7D_6E619476_89085E9A_95986F93_8724658B,
    256'h3E131280_7B429E01_85730B35_26759750_148C1A4E_32418471_2F57408E_9D464981,
    256'h8868112A_90077A34_2E237938_5D28914F_5A7C746D_671D594A_528D0405_1F3A3378
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h0DAC3230,
    256'h93759EBC_8B6A87B6_6F0FAEEE_F05EFDAC_7D8E2CC0_AE938F17_59A842CC_DF4B2EC9
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h66229751_9A6C0F61,
    256'hDA396B6B_90BDC04A_C9A7313B_1F582BA0_C8736FB1_C94B5671_B20AC9A9_EDC88E2E,
    256'h4792ABC0_04B80ADB_CD46696C_211F09A5_706672B6_C7E94C72_103A61B3_183F0159,
    256'h99B1E056_95C1247F_08CA5006_4CC4C5C4_D70B2B94_20B5C56D_0E71298B_3247A729,
    256'h9B07CE30_85ED74E4_D4E6B58F_D9EC0625_21D4A864_898917D0_407710CB_953D9468,
    256'h5F081F04_2C2A6818_C25AD189_410DA72E_B5C9BCB8_AC0450D5_C798D60E_9873B193,
    256'hB952621F_4800168A_16259AD5_22A68B3A_8F4CD5F9_660F29C2_990E2D9A_D7B67717,
    256'hC1F0876C_3C6BD093_B5C8A783_6AAA3B48_5CF49E03_84608274_4813ED81_0A6E34DE,
    256'h3C59FFAF_205525FA_7DE9B64A_53680F23_74F955EF_89047868_A3A30197_9AAA2022,
    256'hDB9E82A3_AADE30EC_30B9AB8C_4D2AFAF7_09714559_554D1794_80E4A951_56A46140,
    256'h4C44F845_018952C6_FD5E2814_31254480_79ECE685_93D97C8D_C340D4C0_886286F9,
    256'hCEFE5A1F_54C5AA15_C592428D_95D67B68_17316FC2_CE97262F_F8817469_1FD5A672,
    256'h42CF8009_896DEC51_C2F9ACC6_791A6F41_E55AB20A_9C24F5F0_2CA4A130_9AAD7945,
    256'h2AE16374_43D65565_7E2F6412_F42809B4_29708992_D3451BBE_A0206553_834CD1EC,
    256'h5F389BB5_B0132E12_C379D240_8DC358A4_AAC4E4FE_51B40793_DDB34E99_6026147B,
    256'h074B31E1_5061298A_7704AD90_C14843DA_8B205A3A_E8A6C6EC_9D8F4182_740627D5,
    256'h3A5E924F_C89DB81C_63221932_8568B632_4E861EF6_F841601C_11B0408D_906201D0,
    256'h7A24756C_28545B51_12D620C1_B09E86AB_CA68AC32_67CBE23D_1DA0A91A_246A502D,
    256'h24A0C11A_CDA7FA8E_B5CBB5B6_1A350F05_FCA10D5F_C9970578_96A79D4D_A10339B6,
    256'hA350E30B_B9D7B040_E8E09663_A6902EED_6E884615_D9C01101_BABF5CC2_0A405BC6,
    256'hAD4BBD71_AEC4622C_1D360FD2_48EF205E_BA82A891_5F319248_37C5545B_0C7DA714,
    256'hDC942F2C_A7EE8513_1083D558_AB8F1725_A3871F10_564BA310_05F8248F_1362B10E,
    256'h00EE3982_3E078B24_5C624471_187EE581_09C028A8_70E3788A_640E2EA1_427FBC70,
    256'hEAD242BA_45E1A46D_ADC00381_EA69CBFC_0CE5BC96_F79A9F13_5848D62F_4697576B,
    256'h180DCCC2_5E0B576E_4A0D1F4B_EB2052BA_9119198E_612AC110_D0CEA5A9_32BCA232,
    256'hC8E18D45_3A1381F8_99145AC4_F2C68A9B_27E69D83_82277EC7_2D27EB7C_668865A2,
    256'hEA541F0B_DA66673F_8933EE80_3EB02579_617A4B74_91C72D58_1A1CC775_65CA20A3,
    256'h824AA4A5_A694AE7B_11057092_6B864A97_465232F5_552014BA_171D6CB6_4E7C8D26,
    256'h644CB62A_5DE27DB6_7620C160_3AAA40CA_6AD3A855_0C3D6479_1B93CC3E_B451C36D,
    256'h23770FF4_894463CD_75B9AE24_679C28D9_40D8651D_603B1878_CF1D0AEB_1068E15D,
    256'h831642E6_1CECD342_2CB3E783_3E402157_A176BD46_65B0EDCB_B75BF278_0F6F5F27,
    256'h76A48785_695A3DC5_4CA71A58_7594C12F_100E6B08_76757BB1_2070685D_C5371054
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h4EEAB2CB,
    256'h48658673_C5090FD0_3A669107_9F269A2C_4E75E01B_250EDA18_45A3BA41_613CFF3E,
    256'hDBF802D5_71E7CE40_3175D29C_8626841D_A8319954_BAC164D0_43F0E2DB_0EED7DC7,
    256'hACC05B04_2A3B0D84_089FF2C4_4E2D7678_924D4FA9_9F1120C5_235AF18E_EDA8546D
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h9BF4B091_CA466A08_C784DCA5_9CF09B0C,
    256'h554A7B15_B6A3400E_511B37BC_441D7D7B_B9CF523E_67CF6DA8_1253EA22_D8AF833B
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h45EAFED8,
    256'h61978127_00D8B205_4A4E2D7F_43F95857_4F82C637_C99A345E_C541EDAA_20BB9295
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h12B6_D9A626A2_B2D8A252_78024212_B63C3D2E_09E0B008,
    256'h7C9FBD9E_68C800EC_F23CB275_2AE36BF9_ED0EFE57_32BB98CB_A338F248_214A141C,
    256'hB117AD08_5A497889_CAA171C4_66A0354C_1C306BBB_58A0C4E6_BF4CAA25_45A829E4,
    256'hD496C564_D0F58B2E_D3185B86_E02D668A_FA069A7E_52F02C85_004CBB4C_26B79F04,
    256'h861C14D6_B33A948F_E0E8D10E_20F39F37_69E765C3_6958E1AD_2B85E5C6_9290F626,
    256'h0045E1C9_698A0968_581BB72E_E6E44CA5_3A0C2294_C8366830_52D8BD62_AB444246,
    256'h706A400F_821119E9_BBA8C280_01A25049_E842C894_0D546C5E_1990C6BD_3AD0C0BE,
    256'hA2895222_654AE886_85834C18_242C0993_073307CB_CEB9A92E_AD2E05DC_5DEC2323,
    256'h36C22B3E_1DE512AB_B4C152FB_63C366F6_F6AC7425_3A738A83_D1CA4BA6_6629190B,
    256'h0AD6A01C_22B74A7F_298745F6_C984B73B_085808ED_07238228_18391C52_75E9188C,
    256'h088D7D1F_9114837A_BEE55F0C_9B2CF58B_6CBD7281_4AC5AA77_304A39D9_4DA3B4DE,
    256'h1217B938_7605A2A9_F0040341_CEF8C4AC_8DAF263A_BA2E7297_1CBFCA2F_9101D258,
    256'h0892A71D_B84582F1_C76EB258_D243D088_C5068C3E_8CD51385_50D02B55_BD4FD82A,
    256'h39A4285C_463D37E6_CFD6501C_DA5A7157_0855D1F8_7132917B_3A10EA53_547D1EA1
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hE4AE650D_2B50CA8F_489D292E_9862AFCC_EDA08879_665D59A4_DF2086A7_684EDB8A,
    256'hF255EE27_FC255851_6741FFB7_E78CAC14_A299C607_199F7091_96F931B5_DD107AA3,
    256'h3EB1B6A6_814706F5_A56B4C1E_A1B2386A_36D4CB39_A9AB7C92_1C951BF4_D3453D40,
    256'h9453FAEA_782F161D_2DD62315_12E0E94F_04BA00BE_C36080DE_89F89E4B_D977FB26,
    256'hE29CB842_DAE6FE0E_D58B1F18_B3326D87_57EBBC17_7B495E22_4A71EF8E_0BAAC23F,
    256'h24BB525F_D705C785_0AF32830_2CB4E356_0184D2C4_5A356EBF_7661DC97_C982B99B,
    256'hD13CC1F6_0854B07D_37CD93FD_098D1A0F_BD647F43_13C02183_CEF17572_63CF2AEC,
    256'hA802E146_E8E5745C_5B7E44D0_F70CC890_34034DF0_11C5696F_333A9AAD_3B736CD8
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h00AA_49694F4F_35C8DD54_AAAE054C_C60A5EC6_96539D52,
    256'hB76DA198_808F9A41_FD1250AD_06C9D2B4_C5A30780_9A871775_1303156E_26B9DF51,
    256'hB2666110_8D6F37C0_E2C69891_E5088236_92A2AEBB_88D55153_7D88D370_A263D6B9,
    256'h5606D102_409B1A68_3A490AC5_2E44F502_F0B82B2E_B56EECF5_647196BE_C13E90B1,
    256'hF6D42E74_2C5AB664_E6E59256_975207C3_0A8EF0B8_0248E90F_C6221014_C88462D7,
    256'h3EC22DC8_767082B0_079F9449_1780C1F2_5EE26E41_65B3792B_C6CD2047_8B97EFCB,
    256'h651C864D_5216EE83_3AFBDC64_C0554E18_E916989D_84F45CAD_194E698C_1D014583,
    256'h289DA763_9351C2E7_7288A053_CA6C6D24_6AAF59E1_E4743162_725F098F_41837640,
    256'h69C806BF_530331E1_D8BCCD59_4B4115ED_B8CAC16D_3364DA5D_8421CD90_96BD443C,
    256'hA6D009DA_E0B2C34A_1D2EACD2_B8961267_9102222A_D6E9F85B_3E58D89D_12E31A4E,
    256'h423C3661_13D2AB55_FDAD3060_DE93B5D4_08A46D3D_293F516A_1571001D_0D1F0A91,
    256'h411B5A8E_84EE41D8_6E17C4BB_E0BC533C_37C0A108_BDE65241_ABACD749_09638C75,
    256'h0E8E8FDB_CD88D310_EA029911_4EED1461_59E6550B_502C0F66_81E91CD2_1C186267,
    256'h1019EE69_50528C1F_CF032B80_16FF1219_2ECAB942_70D001A7_518E1415_4878509F
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hED46051C_8A570336_B49D386C_69D93864
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h0A9284AB_703CCEE4
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h1FFF9CB9_84752F8F
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h899C6BDC_76FA4209_82692A04_CD1B1D60,
    256'h114697E3_ADE1F276_7B2AB0F7_F9E43EE4_F55D58CA_20B0FC00_CE6135CB_D6529EF4
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hBED3DFC4_41A93874_42D3C987_A07A5472_96F660AD
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hE47AD94F_5821271E_989D6BF0_3E6D542C_A581A594_A3386C07_0F167A20_A40E1D28
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hBA99DCE5_06FC589B_E1DE2D8A_B7AC5145_761EEC82_45451D88_E292D0B0_D1B10882
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hA692C834_639F6783_25EEA439_47620421_0404C00B_6F6EFA39_97E2B24E_53C49217
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h9FE8105A_C442A5EB_C0F3D851_63644ADA_3407543C_75421F2A_ADF4C089_2E3F7B37
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h84405243_A4AA4FB8_970DF6E0_F78B6434_10259E59_CDA4FC00_E7ED6728_6F310752
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h618844D2_F81C1925_5FE753B7_995CCB8A_2EEC70F2_2745C139_DB09B25B_0FEDC9F6
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h1C67905E_31CC3F10_03D7AB63_75B104A4_631FD6E1_F9A5CACE_A485646E_645F99C7
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hD1B6D15D_F879CF35_959C426C_B94046BA,
    256'h8D481EC8_854002A8_1E9142AF_6F4979CB_F7FA885B_54E5A543_09267063_5EFDAC15
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h8C874489_731AAFF5_96844A22_55800FEC,
    256'hC42EEB5B_0460F67A_E2FF4389_C0D614C4_EA2C7AB8_188EDF81_97D16AFA_B1A92765
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD13B89FB_9FB19038_E92F8A0B_479DA25F
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hD6F656F6_6DF89F4D_9AA5BE60_6BEDFB0C
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h84F34C97_9B616815
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hE6DB025E_3FA1E154_2F7DC211_1A8AF2E8,
    256'hA6AE24D1_FDD92A93_8A931679_910B8303_94625D37_9DD9353C_50FF0660_1BEF1F33
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'h68F66822_DC293E99_94114ACB_4786C929
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hAC237C29_58FF0FBC_9D282F01_B3DE6CF9
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'hB76B3B12_13B5E18C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h08F26237_147A110B_33013767_19C518C3,
    256'h4F0B39F9_015EFB56_E2154549_9ABD6B7A_36987EDB_FC3CB994_829EA75F_ABB8C8E0
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h6166D362_FBFFEE75
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'hC4523FF8_4A85FFD0_9D820F33_DB35128A
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h76EFB984_DE24FD55
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h2D8F501A_3B03B743_30F2CECA_6554AE38
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h9069B37C
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hF5316D35_3CAABEC4_3850204E_605F79EC_4659ADF2
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h171E38F5_809CA85D_4BE0BCB3_26AF7A8A
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h39C0ABAB_0C85B5E8
  };

endpackage : top_darjeeling_rnd_cnst_pkg
