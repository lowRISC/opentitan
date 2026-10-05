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
    40'h27_62E7AF02
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h5A57_8D6125CB_8D59C808_A8033131_DB014651_3C591074_425A8A17_E639C181
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hE6C540D4_7A3C4757_EC8A8986_B08FCB77_D0831159_F3250B81_3449C66D_CBB021F7
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
    128'hA92CF5C0_C6AE053B_995562D7_FCAF6DDC
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hA6200365_5CEB43F3_E842F268_FBE26BDA
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h6F7FB2D7_F5C5A0BC_44A9AE1E_094D11EB
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h4CE4297A_9B8EA751_D5730C85_237AB633
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hC2708041_6FBCBCA0_4BC1FE5D_4087C45F
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h755D6824_EC5D5E48_742DD52E_434B64D6_9E2E2FF6_AD2C726F_F1AEC646_8A27E6FB,
    256'hA3203934_135D0EEC_1A8769C1_E22FFBC6_D0CEE959_7BAF791F_6ED7367F_F7E88692,
    256'h07ED071B_D7BD883D_2D8A3E9D_0C7E4A8F_78EEA3DF_9D86C2AD_E75496E8_F543D091,
    256'h0A1137F9_7498FBEA_5BE6C6DB_05530792_B7DA71DD_3E63D444_A8F8D318_72788BC8
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h72F9B803
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hD757F336_FCAEE568_E28EF132_060D450C_0F34BC48
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h678158BD_3A986632_CF85B52E_793A85A5
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h2043BF04_BF133533_A50D0993_FDBF7804
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h27CFD6BD_8A063C51
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hC60EA37D_1049BFE0_EBB80796_4D9155EE,
    256'h6692C97A_3421C87F_1ED3F563_0E77DA92_CDE3C32A_6E453D28_40A59E23_86750B33
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h63630580_BB66965E
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h711B4329_9F2BE52F_A055F3A2_EBF8C1AA,
    256'h71F2D68C_4B378BB4_11095324_26167BD6_B714CEF0_D9B008B2_F9A47735_D43E91A1
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h22FC02F2_737854B3_BE06B404_8ACA800C,
    256'h79738F7C_7F7F44B5_2B283B1A_879C913D_99869E66_31B4585D_4B7A24F6_AEF5D585
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h7CB5C928,
    256'hC0A1A9FE_5D3879C3_23C72ED4_347A075A_F12A1168_2ED0938D_747481AF_5EE3B4FB
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h140E738B_23197178_453E9339_5430877B_168C8F7C_7677651C_6E4F1850_11908A38,
    256'h97617446_792F1D24_3D0C2D5E_6C949669_3F6D4851_415C139D_598E3104_867F0A81,
    256'h522E630B_3C7E987A_364C724E_80211253_0557421E_60293237_5A883B01_079A2000,
    256'h5B2A3335_1B82679B_4A220D91_4B402C6F_2B061F58_9E620843_561A898D_445F6A55,
    256'h15260247_1084093A_99684992_707D2725_5D758566_030F176B_4D9F9528_349C6483
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h5FFE85FF,
    256'h7E8747F1_A7D617AC_1C0E61C4_2612F0F1_FA533FE0_5F758B96_21FE31C4_C8719432
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h0D1175B4_602870A4,
    256'h3446979C_10C28436_05608898_292007FE_A373F186_24126006_28B5050B_CE9B2D7B,
    256'h9B5900CE_59948DE4_3EE9B89B_27ED033D_E953F31D_9E2EB694_3B281D16_74C77740,
    256'h5135C278_633B3B0B_1A6B07C1_619CC471_75B8814E_E2E02DA2_1964A44A_5DEB6220,
    256'h116F644B_993021C4_47205254_DF9B0314_64D43692_30A465D2_50103318_84999B42,
    256'h0892DD44_5BE771C0_65365723_7D2D836B_3AD4E8AE_D4042CBC_150D5009_7FB2A29B,
    256'h4CCF1ED0_A2B0E0A9_9921E683_235697F4_F42D42C2_96BFB15A_0869BA75_4A3902E5,
    256'h241A9452_960F1CD3_F8C559EF_94A97E38_542BFCAA_A1CF22F4_9D71A0FA_F54BA098,
    256'hD039199F_9E956975_3767FA48_7158C373_CF05C7E5_A472EC70_D5985256_4D91DAA6,
    256'h3E44D100_A99825DD_A6882E44_662972FB_BF8250E4_1C936718_392C3914_DC118B91,
    256'h80D582F2_8E18698E_A29EA978_7457A6E8_6AE07485_5550F417_2BD58656_D27EA768,
    256'hF6D447CB_12104C23_07773270_16D066E6_A12B5AC8_6E457D23_FB5A2621_5B0574FF,
    256'h2BB15BDA_6FA16816_52AE81E6_84882B55_E1766442_084C6302_CC781B57_8CD7ABEA,
    256'h48E9320C_52F5AE74_9095E4E9_9C8B25B2_04C88794_E759C47D_F0E44945_65F01544,
    256'h7675D335_D0271A24_88EE2A6B_CCD4929E_5EA31100_ABA02113_8835C59E_46FE3203,
    256'h0CA714DB_C1F0FB36_D57A91E1_388292A2_831272C6_91B99451_9321FB12_ADA68C97,
    256'hBA2510C5_0BC01BC0_8D494C7D_4BAF37CA_34C226E3_6AE77D40_F09AC31B_0249824F,
    256'h938930E8_04404202_18CE848B_B08D9ABD_1AB63073_4004B8D4_1E686EA9_F4808589,
    256'h5C7AAC39_D626D965_1E85C2C0_784F6901_2063A315_205A897A_DBE29E37_9910CC0E,
    256'h365E5826_A98E72A4_3AF97D1F_EDF4E658_26AE48AC_4141CE38_903E924A_97F27567,
    256'hDBC01853_799C7074_13304EB2_79F1B5C6_E55A9D06_A9F62B17_BBDEC126_03957118,
    256'hBEF73083_FB82DCC4_26CA3D4F_1D41988C_A243B068_619E0A2B_282CCB02_D3CAAD68,
    256'h605DE764_ECB6A0CA_A89979CB_EB3D474F_9B73E818_90657C49_D47D8387_38099988,
    256'hE9AC6639_6BA022B1_16AC8342_1C5C0729_45C98E51_56EEB99A_518590A8_2497C68E,
    256'hD1810A64_ED870DB1_37CEC134_9B37709B_B7AE39E6_611F16A1_154899E7_C4860A16,
    256'h578C7061_809AE029_7674D277_009C4128_E1F93F61_11A346E8_B65D0530_F84AC9F2,
    256'h3DE55CD9_117A9981_A93A3483_519F8A62_F59A8642_5928B24B_6C656C16_28A842A0,
    256'h4D414426_F8C314A7_62FC60C6_72C90257_2FD57E19_A95AD7B6_13807096_9A0801C0,
    256'h02E97174_9A830CED_5BAF1A2C_5FB6CB98_9EE14595_0B0A5005_4553AA20_5506AAA1,
    256'hB1C6CF10_C891616B_4950B30A_53100E3C_3E6D0825_497A2C6A_DDE2BEA7_BB1DA7A9,
    256'hEED97C6D_3D44F2FD_8F3BE947_7DB4B612_53C14192_D203DA47_1ACB4359_2322CD33,
    256'h981F3730_DA71CB4E_1667BF00_005DBB75_34884FD5_6C6F88AE_EAF08A4D_DFE3EE2E
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
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h1FFF9CB9_84752F8F
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h899C6BDC_76FA4209_82692A04_CD1B1D60,
    256'h114697E3_ADE1F276_7B2AB0F7_F9E43EE4_F55D58CA_20B0FC00_CE6135CB_D6529EF4
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hBED3DFC4_41A93874_42D3C987_A07A5472_96F660AD
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hE47AD94F_5821271E_989D6BF0_3E6D542C_A581A594_A3386C07_0F167A20_A40E1D28
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hBA99DCE5_06FC589B_E1DE2D8A_B7AC5145_761EEC82_45451D88_E292D0B0_D1B10882
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hA692C834_639F6783_25EEA439_47620421_0404C00B_6F6EFA39_97E2B24E_53C49217
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h9FE8105A_C442A5EB_C0F3D851_63644ADA_3407543C_75421F2A_ADF4C089_2E3F7B37
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h84405243_A4AA4FB8_970DF6E0_F78B6434_10259E59_CDA4FC00_E7ED6728_6F310752
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h618844D2_F81C1925_5FE753B7_995CCB8A_2EEC70F2_2745C139_DB09B25B_0FEDC9F6
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'h1C67905E_31CC3F10_03D7AB63_75B104A4_631FD6E1_F9A5CACE_A485646E_645F99C7
  };

  // Compile-time random bits as a field entropy alternative seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeFieldEntropySeed = {
    256'hD1B6D15D_F879CF35_959C426C_B94046BA_8D481EC8_854002A8_1E9142AF_6F4979CB
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hF7FA885B_54E5A543_09267063_5EFDAC15_8C874489_731AAFF5_96844A22_55800FEC
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hC42EEB5B_0460F67A_E2FF4389_C0D614C4,
    256'hEA2C7AB8_188EDF81_97D16AFA_B1A92765_D13B89FB_9FB19038_E92F8A0B_479DA25F
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hD6F656F6_6DF89F4D_9AA5BE60_6BEDFB0C,
    256'h84F34C97_9B616815_CEF2C4EF_6F019905_CF0F143E_1690769C_DE173DE8_94DE60F7
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h5139BD9E_C081E92D_1365795B_312F3098
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h77931A93_3F69487E_3E530377_D8F6A201
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hFD6631C9_8F3BF180
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h7A9D3F8E_2B320539_E0E893BC_16F5065D,
    256'h0A9CF421_DDB8D6F6_E4BE035A_87F1FA14_52EE598F_288CDAD7_790CB40A_C4619C15
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'h69644AF4_165684E6_B8957AB7_3FDCB809
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h95B2775B_C9E45756_CE39733A_59B3B534
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'hCF161D0C_817167A6
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h47C42CD9_AFA55CEC_C56C10A3_92BF68B9,
    256'hE98AFF41_885801EA_C0B549B7_28843790_E0EE148F_53177567_8718DCC7_E7EAF4E9
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h2E858E79_761BD2E0
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'hC0DD526D_906F3717_1E38F580_9CA85D4B
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'hE0BCB326_AF7A8A39
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'hC0ABAB0C_85B5E837_8D2A113C_064F5A41
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hA1EA075E
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hCC883175_73DFA87B_970DB22B_C4C60153_34E03FE6
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'hC6DCFF99_3B5A4D77_7088BBDE_C26E61FF
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hA526A98D_294DBE1E
  };

endpackage : top_darjeeling_rnd_cnst_pkg
