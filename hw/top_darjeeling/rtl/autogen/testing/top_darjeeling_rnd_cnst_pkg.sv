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
    40'h16_3162D98E
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h99D5_C22CF8C8_6CD6627D_E9C32856_A5551496_90140701_48213137_09384198
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hE9B374A3_636A66F9_69AEA3E9_8FC6F489_2BEB458D_5B4BD644_E79A35D6_90BBB852
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
    128'h739DC155_FEC8B9A9_CA90AFAA_4655965A
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h49D16AC3_5F3D22F5_CA036E02_9DFE3E01
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h3F88514B_08E645BB_A939B145_66456BA4
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h39FB382D_362730AC_A45340F2_B0EE60F2
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h5E2CEE80_A251609D_5DDA4A4A_D8C83D39
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h7D1F83D0_345AEDBB_B4D7AA71_9297D83A_E6DF7CA6_2C4B0BD6_EE484A7E_AFE9079B,
    256'h80932F7D_9EF197BA_49CEEBED_E8F7A26B_19372684_CDC4422C_133B9D9A_6699B6C7,
    256'h7A29761F_9598107C_33B11AC5_761C1498_1AEAC9E2_8F9D016C_02B80B15_81BA47B0,
    256'h81EDAD79_56485909_768EF3DB_A808CBC6_D57FE748_9F415498_70395C90_D9ABF4E0
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hF5ED5BA0
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hD076DA98_488BFA9F_11D35FE9_02E19C50_C193DED2
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hC90D1100_75FF2D26_986FC601_47EB6D22
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h83F7501A_7DAFE49B_F7A167AD_28AB0988
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h33DC1FBB_0BAC70B2
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h3FDC0414_E0DA5CCE_B706FD7F_44D7A94F,
    256'h649BC808_9D6717D5_E1CAD0ED_6E4B8256_27CEC9AA_F0693ED2_DA022A18_C8B87509
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hAADE3ABC_18D04239
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h6A018965_817076F2_F2993BBA_A73B3D7F,
    256'hE2A55EAD_B5A34E3B_3231C356_B41C5A2F_216D4067_44FDC803_FE4D9040_92C5EB4E
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hEA6BBC7B_14B8D5D1_9561BFB7_38344CC0,
    256'h8CECE408_CD696109_BE20593C_2968FE07_D7DA74C5_2D0AA1D0_7A72EDCA_D492DF4A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h6C33A651,
    256'h3D818939_D376B89B_EBBD8595_0D65CCB8_53536D9B_B0A37927_E69ED89B_AB42E6F6
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h1C454251_46349902_6D077047_88664C49_835C7254_3B9E742F_35366816_6232853D,
    256'h224F768B_8F0C2C2A_01774B03_04897365_1E987A00_7C2E7D28_300B4159_1D0F1F6B,
    256'h2B8C783A_0E408D29_060A4E05_7B123184_44250881_7186180D_8E539757_50902110,
    256'h2D157538_1B24269C_693F9555_7E4D135A_56961987_82095D9A_1A178A27_60439437,
    256'h6A935223_39805F48_5B612079_3C6E674A_589D6F3E_926C9F63_9111647F_33149B5E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h5555960B,
    256'hB2129844_D6433FDA_F01DBD72_8448E762_02BB67B6_6BE08307_B7E7C0AA_9010A8D8
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h72A18A1D_596B1125,
    256'hB88419D6_C3D404C3_22326B05_2A1E2064_282C20E1_9589548A_30A5828F_25C2D675,
    256'h4013709A_984C8EC1_7C3136DC_0458056A_A61BE4DF_67866461_0F91A8A7_2D8AAFD5,
    256'h8AE18EB0_EB2A91B0_AE9BC2B6_39171FD4_E92010AC_038D83BF_5A1C61A8_ADA6D024,
    256'hE05A69D1_B22D7DED_65927E18_0D4950FE_74E624BD_5D81E302_364A2A9A_B1041D02,
    256'hC448BA9A_1CE81C7A_3714EDE8_0D3C1501_1C7D13A1_0C17BC12_C08A21B8_9DA36DCC,
    256'h25788CE3_F6060590_AE1580E4_A9EBD3EA_B1442D01_AC52C753_BC51C30D_961A0069,
    256'h8D49794D_639F2D5B_9D49BBD0_4B4C3B8E_88C6CD50_294F62B1_4FBB54E9_DD5AAD00,
    256'hCB36CE14_092841DA_A42199AA_8C069F40_B6DB6EC4_87ED6274_A2988A5A_63D730DE,
    256'h6E376F89_E16D348E_505E926B_A4134D2E_65DC4315_5C300729_AD7791D1_971E11C5,
    256'hCCB781DB_8091F1F2_F3320561_DDB939F0_3B94887E_14DB1EEA_1149BB3E_9318EC15,
    256'hEA635F0C_30E02F23_CFD73B19_16C34021_C5259E67_B41F354E_B696209E_E0A262D1,
    256'h09586551_510D52A8_B1961FAA_A2166F92_6BB1EE65_B7533475_848EE582_067235D6,
    256'hB976667A_E0F7CC18_085110AE_B34AD420_81099A2F_63461313_8BB429E7_4E59889D,
    256'h41AB9876_71033A16_F579BD03_9D8636A0_3CDA654C_F9AA2D8C_3DDE6470_A2900A1D,
    256'h273649D7_14502B5D_9B5D8E14_8D4B4C30_EAB29C13_3063BCB4_A3D0C7BA_A53B5FA1,
    256'h55A706CB_C1C3152E_85D2189E_050B27C6_12189363_66CC85A2_B6C8332F_4CD404C6,
    256'hC2F1C740_71000616_3106BAC5_7A50FC08_E565C68B_C69D91E9_E8362557_2459C58E,
    256'h9559248F_9F64A115_86C82C1E_A6451AD1_3CF0AE54_A1AA1DA5_6E9892C4_5AA4F9C0,
    256'h759D2314_6D991A03_D9E84D87_2967544A_00ED2A38_161FE6C0_BA5F6424_5AD69E31,
    256'hDBA6D125_299B6735_D4949F20_892221DD_1B7D5B43_62F776FF_7E4F41BD_FF1F5652,
    256'hFD743422_627D1AB6_4B12E2FC_2E4B7A22_4024E175_F575415C_233E1F85_25951EB0,
    256'h9A478B09_A3C49952_0283B80B_36DEF49D_89459E0C_77F048A9_5F3C6895_E6578E0F,
    256'h782C1E8A_0A9A089C_85632B98_1062EDA8_D876C464_DC003A41_C154F99F_691934C5,
    256'h68A7D295_0E51BB1C_CC21E116_8A03330D_4988E651_72B21AF5_10DCB2AC_5A465025,
    256'h600602F7_979BEB1A_F0834AE8_10B629EF_2072065C_31378E09_8200D9FD_5512E977,
    256'hF225485F_59F699A8_EABBEAA9_A85B1532_609217E0_E406389F_02659A68_9EC224CA,
    256'h11CC9770_9151AA2B_D43E5FEF_B1240FBA_0584E08B_B2E0155D_D66D4307_1A856A41,
    256'h322AE367_57BBB945_92C437F8_C43C9343_392CABCB_E721EA9E_43C190FF_704FB0C8,
    256'hABAB4C25_99E44F5B_F8D2640B_2E43AA3D_3B9B809D_0899D853_9AD4B271_02BCF80F,
    256'hC6D4790E_178D6681_3549E215_229B5024_3284904B_53F93ABE_00879C05_8886917B,
    256'hC6BC01DE_991046A1_AB7378DA_101CF42E_4CC6E1EB_FAE296D1_C20DE59C_4240042A
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h27843EA2,
    256'hA0163EFE_DA5B24D9_3F97D62D_99C96054_2F4A1F25_95192E9A_969A8854_19A9D57E,
    256'h36519FA4_2D20EFA3_48CB77F5_089A8381_B62D9717_B3647E5C_E0796CA6_8AA29523,
    256'hD3F94F27_C74ACAE7_6B3E1453_26741F80_4E3C3A34_51469C61_18FA23BC_32E428AD
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h36556E78_48A16CFE_DF50E16F_FADC7323,
    256'hDA7CD280_A42F0623_44681A01_766C772E_769FF701_243ACC43_79AA1D2D_7A4D6E0A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h469D8BE5,
    256'h8D526100_D826EBF4_137728E9_93B979B0_5BDDC26C_CB34AAB9_3413F8B7_DC7CC8C4
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hA5894B32_49675262_B3089628_9F5B5522_C7E760A1_F4993113_E19CDC9B_7436983C,
    256'h7B3AC16C_78047C25_FE5AE06F_0A37BA85_D063E8F8_D8DFD74A_5035F26A_AD640F15,
    256'h7FB48D65_AC0B1210_D4EF5E9D_3FFBBB94_0CFA4276_8FCC845D_21546633_9305AF3D,
    256'hA4A8B001_A2F74756_7E1E2DAB_BD3077CA_8A3BF1CE_D38CC440_1F41E486_D5B72057,
    256'hC52679EC_0951D24F_FC6D3E2B_43CFC058_F9DAEEEB_4CD6072C_757DB9E5_18BE7344,
    256'hB1531123_82FFA090_19A7D1FD_ED2E278B_C2B202BC_70C66B16_92CBB588_D9340E87,
    256'h065C911C_14F04872_CD8E7145_C36E1DF5_E6F680B8_1746E259_1B2AAA83_24005FC8,
    256'h68971A38_9EC9E3A3_957ADD69_2F81A929_DEA64EB6_F3EA61AE_0D9AE903_4D39DBBF
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hDE05CFB0_93C70D4B_54DC8AFD_1F075326
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h71EB83C8_20E1F1EA
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hA3A18AD3_4D471B19
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hED00162A_53AAA26E_1D23467D_25516B2E,
    256'h03474938_BF8C4FBA_6C331FCB_7CEEE5AF_1E864506_D570B147_006D636B_E93EC727
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hCB34036E_CA2E29D9_B56F71FD_0BA464E4_BF50C448
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h105D80C0_0220F1DA_1D3249B8_B27F540D_01C61267_36232F99_13430791_75C6A3F3
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h6D389BD5_D0A06E31_4F7E0EFD_C7B7970A_3EA73511_6A0C6B28_F2300DF4_7AC9287A
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h219E00BB_035F64C9_4DEF907A_59C5B475_DB2D4DDE_E65528DF_B5418D87_91A40518
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h626BFF09_1F1BD0FB_AE67415F_DCA0E742_27478F3A_0D0E78F4_F82AE004_FB322A9D
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h35FFFAE3_0FC86D8E_A37BB7BF_F6C6653C_DA8E066B_989FB2BD_83BEADCF_1AB87127
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h0CC1E537_545255EE_F8BBC56B_206E0081_62473AE6_CBD4926F_66ADEAB5_DACECEDE
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'h39F5AD96_335C4709_F70E3460_D37113ED_DDAF0D2F_EE3DFDE1_D0669984_352FF4E1
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h3B0CA88B_5A2EA38D_A2B1B9D7_8968BBCC_29D9A9B3_3196D98B_9EA0DD85_11D5894D
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h8150641F_408227E5_9F67B6DC_36409D3C,
    256'hD85FEB1E_E319926B_E21C6829_53B498F0_978818DB_9932D613_7CB3FBD7_9C1473B0
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h6B9F20A2_9EABFCBB_C16B3516_4D75EBC2,
    256'hE3B50AEF_A1CDC5B5_60546374_109C213A_079701C3_AA6613CD_1583914D_8107F533
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hF051DE95_EFACE9A3_F55549A9_B7B0AC9A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h3AC6D3C5_D2386E06_3E354FEB_30B31B7E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h7ECFAE01_577C7FC1
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hF7536C98_A2EA6BEE_08F2B89E_8D21F35F,
    256'h1B9C1680_797C96FB_A6755DD2_5932B6FD_8E5184D1_004086FC_358CDD03_E0870E99
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hDBD995DC_1C58F0CD_F7FD1D96_CD7FDBE4
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hE4C18945_4CEBF75D_37F28396_B53D310D
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'h4457746B_FF3406C1
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'hE27EE984_E36BCBC2_2C78AF40_5CB59C49,
    256'hBC424EE1_07A39690_25488663_E46F95FF_CCD43DC1_77A3C58D_5674C2AC_E09B6B64
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h710745C8_E815D38E
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h66A9AFF8_260EDCEF_14634261_4F489DF2
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'hA995C61C_AAFB48C1
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h8FBF2519_367CC435_373D323C_968F2690
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hBB99EFA4
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h9C764A7D_80E22E35_6A07B35E_9CE02231_5DEECAAB
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'hD9518FD8_02ED5B54_6C9882D7_8B7218B3
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h066AAAE3_CAE1655C
  };

endpackage : top_darjeeling_rnd_cnst_pkg
