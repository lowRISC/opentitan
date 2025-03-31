// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047


package top_darjeeling_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h4B_9FBDE86F
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h0673_65393414_70210F61_F55284B5_9A44A0C8_1DD91B00_62628D79_A014C799
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hE8F2F8BE_62FE9D2D_4204B2F5_4BE875AE_48027768_0CBA442B_AA3ACB9C_2A3F40A5
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hE816A506_C2AB1F4A_2F01CBE9_08A34C2A
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h20FECDA9_A5FCEBA6_80BBB8E9_C0F3699C
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hD9803542_888FA690_C16DD41B_3D1FA05F
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h7ECC8324_5CCC8577_DAAFB97C_26A70119
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h88481250_C2C82DEB_519D69C7_051AAB9F
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hC45A1658_FA9063CE_216C0B41_2615D73F_476529A9_6A1A8ACA_4B0BDCBE_6B240C31,
    256'h095162E4_1BF99B2B_C41E9EDB_B4685F7E_B27EB3B3_5F352752_E34F64CE_978305BF,
    256'hC3481A21_62EA2792_B7508F1E_AB067AF9_54DDA549_1439A9DD_E6320801_FDCF25A4,
    256'hFBA52839_9117069E_77C887F5_3DDA6FB4_EF8758B9_9027B6AA_7468BC0B_D8D70368
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hE7CFB11A
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h7C7F6687_8056334B_97A7D386_9812A696_D1E12D93
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h7B2CE9FC_83DDAF1D_D8C5A42E_2AD24FA0
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h2221B6FF_5AAD7A9C_09D5D9FD_D1CFCF51
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h2835C0CF
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hE87D0CB1_0F19E4A0_18824F2F_F75B6B6C_693C68B5
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h9864FD4C_E49D2CFC
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h8777ABC0_15988E40_CFC943A7_A17E66B7,
    256'h177D895B_35BEE482_185D1F67_BFFC2CD4_C72A0ABE_95A33822_9011736E_90244CDB
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h9AAFC50A_72F0BBE5_5FB10265_D29883CE,
    256'h15B713D7_8A1FC640_6124646E_3ECE32D0_5C1BA3F1_36F77953_84E0AD7A_356B2D88
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hDC0DC524,
    256'hD3B05546_03562188_552794DD_2BEBF67F_318B5A49_0E55F7D8_B8325652_A92482CC
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h4A970275_7C9B5D49_28562612_1B776903_7F89926A_8B4D433F_7948722F_81141F7B,
    256'h5F93007E_54632A91_5336257D_71176B5A_1E133195_5B6E9644_607A5780_9C765568,
    256'h6F3E4527_6C66860E_076D629A_4B98583B_0F651019_74294C8E_9E332B11_709F1D61,
    256'h992E0B16_87518A8D_06323904_21083D82_78418459_94200967_9D85500C_4F384290,
    256'h4E3A2205_23883C64_405C3501_245E2C8F_522D4783_0D151C18_300A1A73_378C4634
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h813C2B4C,
    256'h006E43BC_22B155F9_A5BA49B8_6B3C2014_09F20381_B6FFCBA3_C8388570_79768444
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hB8B04AAD_5251E951,
    256'hEAAC2128_1068257E_EB1066FA_05C9B628_E30E1CB3_B8601DE8_C4200716_6C28E1B6,
    256'hB4A34899_213EE696_26992A4C_E56C2434_02A86AD5_5505A847_1A355369_FE3E672B,
    256'hA225160B_DE87206D_08DCDB42_7DBE26E9_82AF6A56_4A9B1D7A_C506956A_136C5888,
    256'h3C0515E6_38A5B5A0_055EDB8C_13812467_C015C18D_56BD656A_24E676D9_0089334B,
    256'h6EBBD23A_C4A0B581_CA1B9F58_4CE0A2C4_7178B9C5_22379AFD_0866A238_7FC61A31,
    256'h9AAE5DD7_6680939F_1BD36CA4_3FB08901_1C0315DA_1ABC2DED_A9E12777_0CC8A20F,
    256'hA16DE812_87004FC2_7C6F1E43_67385B94_C71A29EA_A0969786_DF9F8B21_7298C716,
    256'h5BA21B4E_4020D46C_B9F159EC_3F564552_78726503_70C31153_11F42A08_5E14D15C,
    256'h5473D851_90AB7971_3361555F_A0378CDA_4329BB66_FB437101_D4CA9C15_8071CC9C,
    256'hC7602C1E_5FF02649_8271F172_FD9A7FD9_12B63614_44148AC1_04B0CA10_FD17ED1B,
    256'h2506AA18_681A3F47_40F84173_A7DE7836_9C4D04C2_997D979A_F93104B6_21E93ADC,
    256'h3C9AD0E9_286E2194_92B6AF65_28840539_04696909_77C3D759_6F68A141_492C6C8E,
    256'h159903A9_47CA4DC3_22826316_6D3CE9A2_84A27511_974D4256_A242D1A4_994A87E9,
    256'hB1A79187_49883511_502B0776_2F62BC69_BA84461D_4B114431_3EB99E5D_9778C26D,
    256'h5D5604D7_3187E07D_37A21678_C4EAA8E2_92AB0B5A_1255AC5D_B52EC0EC_3291DC2A,
    256'h42F18311_287EBE9B_E4298A49_AFD2E999_51220111_D2C7B8D9_322C4E38_94109E68,
    256'h062B20A6_C333572C_24980557_12570118_4F1634AE_9D4B0921_2B719E23_B1E94D6C,
    256'h6A9D7B19_4FAC19AE_7DA463BE_0E498942_D49D20AC_0240F93E_2098947D_7BE2A48C,
    256'h534FE41B_A5BF2324_39B13C8C_ADD01ABB_18AFC401_C0664F45_1703C7A9_29C4F667,
    256'h99D53C70_ACD0B4C4_867F2B76_844099D7_453A4A1E_DF396E3C_159C121E_E475C042,
    256'h812906E5_00748357_E9497080_9AC088B6_EF9352F9_7E3D54F0_F974096F_B0D4C148,
    256'h2FAF034A_77861E03_6654BFCE_73DDEE85_A4B478DC_394FF5B5_8B236FE5_12CE29C4,
    256'hA33C8516_1E47C612_30E177C2_C40F9109_1091525B_CC2A155E_5AB876B0_7424F3C1,
    256'hB40E4D13_AE45A365_53D56331_1073022B_7B0BA870_9AA46A08_B0782C5A_C0410503,
    256'h8D6A5D98_B990E726_590B2D33_A6F7AA93_B4EAF37D_016945B7_31EA18CC_B6305FE6,
    256'h9DDD7E2A_D600C92F_62037D17_9D0ACAD5_754048FA_3B1B5E91_15B22EC1_67667DF2,
    256'h4C9B3120_132EEEE2_70812F02_E1CDDA46_D3E7DCDD_699B081D_96248C88_DCDE1A0A,
    256'h3AE14071_4B863EF2_50C2DB3D_02B319BA_5ACA5857_09628FBE_62F0A2C8_0C5D15F2,
    256'h0125E80A_880D44D9_5A918463_2359E86B_6E657528_03258D39_8EA98146_A6AA27C6,
    256'h43310A02_C5AB42CE_0A12C2B5_1ACBB5E9_D5412A7E_672B856E_6EDED985_BA7123BB,
    256'h813D6A30_E002CD08_11A65C34_482837F4_ED32F1F4_52645889_93A23943_D83B96ED
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h3D1B23E5,
    256'hBE54B9C0_BF5B2DBD_49AB2284_A502186C_26C49196_24EB713B_C42AE08E_B2A09674,
    256'hC93F8C23_868B5855_34B613E2_828B0424_F0F9EB90_0313DCDD_D6F8207B_25A5B5B3,
    256'hF673BA36_487D1ECA_F61806CC_C0803E75_180AB65E_E3EEEB76_AFEBE2EE_4702F603
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h3EB027F1_AB166FBB_FF8A085D_67DD1895,
    256'h14941382_F15C68FA_5470B67E_621C4C3C_B5DC1B45_CC9339B8_E36991EF_AA290A30
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h42246B6C_385A5AA3_B4FE9C0A_8D1F2128_E03E0B01_632E027E_34C81340_BCFD0FD5
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h3473B544_0B76763B_45BCA816_6865FDAF
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h59F386D5_174CC7F5
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hFD1F544B_3A82C54E
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hFB391F4F_5B077B8A_27F6E309_98B09A57,
    256'hF362C391_AB50FF2F_4BB436C6_DDE929D5_E303AA8E_C846D695_80742118_590DC805
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h27EE88EB_0198F665_F5E977A5_4142ACE1_40ACB4F6
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hC1A49659_2784AC08_9E72877B_DAF9F795_4486164B_58EA68F9_B7F647CD_AFC1C9A9
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h05A7AA52_EFED17F8_EFA13E95_43502F28_C02C460A_A8D2A575_B899B4CA_AE056CF2
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hB85353E1_A33975E7_B1209B86_8A4ACD91_9ED9795D_5F519AA8_CD47AC68_B65650A1
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hBB5A4A6D_BF0BC7C1_C7AF8402_BACD250E_D8960C88_B4B17EA9_867B47AE_9A95AAF9
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h6DBE43A4_472DC0C7_2F2488D4_0CCAD757_5333E5E4_8F00BBC1_F91E5EEA_7AD029C2
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h13141EE8_6E77B99B_F0A1BCD6_7FB8941C_331A4427_7BC08F71_1D2D33E7_2BC40A36
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h399D8364_DCD59508_D525078E_802F91D8_583804FD_E71271F1_738C1CAC_987A6B8A
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h7758B762_216EDD63_070949C7_834AB6EE,
    256'h6E7AD485_FF3CA72C_2242223C_E6D70F17_B4F4B328_18AA49D1_25B4DEFB_1F3C0BE8
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hA29BE065_C26D2355_0BBC139F_F6461763,
    256'hD7E966A8_A7219EB2_E8EF9F11_A152E6C7_1AA23B88_64416E75_0C01A333_9C6C7AA1
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h1244ECD2_8A62CB1B_851078C2_A5F18EEE
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h28D0B562_043B7312_EFAD871F_92E7527D
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hA865D661
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h9839BF5C_89AE64A4_39947E17_63402269_FFA8F465
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'h4D7194E4_707ADA81_F8A6DB14_CA845BEE
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hE6079828_9AD4FB0D_F1768296_39015270
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h0E078EC5
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'h662343BD_21BCC1CE_8FC8D1A4_D77E0B16_CB925955
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h2704F5E2_1287FA16
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h8AF251B3_70D034CD_A6051526_62F4D11B
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h3245D594_3EA5FD2E
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h4BEA016B_7911DEAF_01DF7425_47371445
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hD6E39551
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hB855AF94_70711FB1_5B06931A_78AFD9ED_2B348388
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h47D3D7B7_58B37D1D_1CA19A07_9C48D7D4
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hE67100A6_AAEBE45B
  };

endpackage : top_darjeeling_rnd_cnst_pkg
