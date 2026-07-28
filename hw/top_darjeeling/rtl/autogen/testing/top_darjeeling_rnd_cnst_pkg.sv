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
    40'hAE_71A7671B
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h8260_063D350B_5C535164_774E0E59_0A6A15A2_0A705B78_956361C4_847D020C
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hA077BAB4_02825179_93CBD11B_5411DE0C_14F56DCE_B007F416_13A7C433_535D032E
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
    128'h027AF600_4DB28500_37A5DD46_09C57F5F
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hCDBE0371_7CAC554E_43806E74_AE0341A4
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hE42FA909_1A421855_55960BB2_129844D6
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h433FDAF0_1DBD7284_48E76202_BB67B66B
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hE08307B7_E7C0AA90_10A8D80A_AD006409
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h0F9C7879_7720F7EE_C7473E96_FDB885BF_81879579_49933042_DC73F910_10FB5136,
    256'hAC37BCAD_EFD6E2D4_8CA18FD6_91119991_097A5C01_C5AF19EE_DEBC4EE3_96E076F9,
    256'hCA45DE86_9E6208C0_511E4A00_8FF9B0AF_BD938A4F_C64B6324_3E286F90_F55031A6,
    256'hF3F5C5DF_91521FF9_89F25F88_4B49F44D_62680135_A217B743_B2FC93EA_0047B31B
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h4BF0C90F
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hD29B3251_D28786BB_1A2043FB_C0B2FB2A_7E23D738
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hE319F05B_9901B736_8D256FC6_FE10EC51
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h4F44793E_59B5EEC5_3085AB55_2AC40CB2
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hC1003ED0_FC3B704C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h8456295D_5C42D1A5_BD910D89_39B9ABEB,
    256'hE463825E_75672888_06CC3CB9_F74AB7FE_0D4CC1D2_AAFCCB72_87BB5270_03106DCF
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h2BD4647A_8422CF4E
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hD39CCE6D_CB2BFEED_CA6BCF86_7BA919B5,
    256'h88218D0C_1336807D_7C897554_C1DDBF6E_D4466A96_8A70F15F_82521320_292CF142
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h7033BF90_FEF9505C_26BB21F5_F8605036,
    256'h32F72311_29817BFD_EA15658A_D4A8B1A9_C27DEF00_64AD8975_13136D6A_B8CEBD18
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h29FADE5B,
    256'h2D878123_2BAD834C_D6D217BB_338CCC72_6FB9979F_E548668C_6039803A_D1482548
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h97164217_29569A7A_630D6E35_87866876_031D9059_849F4C47_11057D69_0C741B10,
    256'h5D893B7B_738F0A78_4B6D0912_36212E1F_2A853A46_2B602F8B_1C960643_2C5F993E,
    256'h83571340_0E9C6F4F_777E9D20_248E939B_4E27827C_0F8A5A80_8D983202_2D716167,
    256'h2519305E_66555228_3D4A5354_9E086479_6A457F58_1A396281_3891500B_1E14418C,
    256'h31003301_49951504_655C3444_88225B92_6B3C7018_51233748_26723F4D_756C0794
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h77D08311,
    256'h59F3250B_813449C6_6DCBB021_F7A92CF5_C0C6AE05_3B995562_D7FCAF6D_DCA62003
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h796DE8E1_609E8C92,
    256'hB49E1901_11A8E50E_ACABF479_7751B2F6_4F2856EB_44C669C0_B8C64235_55987862,
    256'h328A7B5C_344EB104_448EA3F1_F81155BD_8082D024_6D27E659_5DB813E4_56E7086C,
    256'h17356B46_4520AD17_B50468BE_57882099_E4171D2A_83381E12_86E069FD_82EAA53D,
    256'hC32198E2_259B6D82_E4A6535F_9913E2D3_8FE70672_F7681405_C26E18D1_4BD25E95,
    256'h54BA10DE_20DF3160_DFC46CE2_46763B53_9ABC5014_5F557E1C_32C71B10_CD01E779,
    256'h329E6295_0062E92C_0E268409_83C88960_97459C78_91823152_43318B97_1363C1D9,
    256'h5B5836F8_C0A280E7_5C6C4B81_28989686_640B6AFF_0A6A4419_4E7C4D29_AE8C1B41,
    256'h5BA99275_00F9B290_71142154_E1A7D0AA_1D56A481_6094207D_13215E66_4887EB5A,
    256'h416A6804_36D87183_B2169354_6A382304_04D9710A_612A56AA_70678958_6ACDFCB3,
    256'hD57A5EAD_6E80208E_B43AE692_B04091B0_D4629898_ABEBE9EB_A865D4C5_C9130F37,
    256'hA573768D_BBCC0C47_60E73ECB_96C1C39E_FC5126F9_C6E11C9A_5011990B_5B75790E,
    256'h69839C04_E4472123_75A4C529_A2C85412_4BE99DC0_4AD0214E_59C641B7_98F98D06,
    256'h9364EE13_5D064DC1_5CA308A4_B508A2B4_CD5C652B_F602EDB4_830AE8D7_016646A2,
    256'hE64EE8E1_38825BC3_FB099F62_6A288DC5_AE673299_D22544FA_E181534F_2C08C8AC,
    256'h9EEC6A5A_51A54520_A3C56EC5_F28D4D43_28CAD56E_05B78CB6_B66E2421_586149A7,
    256'hA084B0DC_E270A53B_2AB30433_6CEC7AA5_677ECAFA_46E8B920_03D9ED42_50081DCA,
    256'hAD5DF754_0300227C_01713A6C_6B7D881D_A519A945_5E42FC77_131724DB_FAA02A16,
    256'h14A00A8F_87544233_C4954784_D8995DC0_64488B19_056ADB16_64B7221A_A2D1E1F2,
    256'h395A1042_92EBA0A3_5842C07D_93D58E03_A25BD5D9_2F0DAB07_B256C245_FB207761,
    256'h1D8A158D_528EF884_DA5B092C_60A0495A_B6EC901E_E010D45A_3592322C_D33981F3,
    256'h720A72D3_8599EFA9_696C5CFD_56EF0229_37C70FB3_1C879FE7_8261871C_05E47DFA,
    256'h85E2EC0C_680422D4_B2DC9F43_E6A9D630_83D5FD3F_4C1F712C_AA6B9AD1_AE3C3EA9,
    256'h93F306C7_AEF0AA11_3DEAE6E6_458EE880_F07F40D9_D6BE7250_513B3031_10E2215A,
    256'h36106130_9DA29EC9_D5DE15B7_70C97E0D_5EE06746_759A0450_74D12EC8_F79EF87C,
    256'hA836D6CD_59149050_E82F29B2_8A053FE9_DADB0F91_E606F308_265AC779_69482186,
    256'hC12776D5_32AEA70D_D7838305_2E90C4F0_28BD6959_0CC49B5B_22324EAC_4665E99A,
    256'h8098C236_BC38C013_0E0C7C0A_EB25F811_E86B8D07_B40F56C6_52B14B39_F1D3AB24,
    256'h9406E594_22A1830E_3C6EEBED_E009A943_5081859E_4660EA58_99E8DEF9_1E83826D,
    256'h261CC940_186550C2_C3F92A17_40D78861_4498F929_4C98C449_110F54AB_786E3D7E,
    256'h6748A0F4_1BE487FC_7DAF5652_FE1D5D0D_02009F46_ABB6FCB1_2E12D2E4_B74870B2,
    256'h4F0A5F61_F5D707A0_6F2415C2_33F1B851_CC51E3A7_A9341E2A_6BC7167F_9A342D95
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h6D389BD5,
    256'hD0A06E31_4F7E0EFD_C7B7970A_3EA73511_6A0C6B28_F2300DF4_7AC9287A_219E00BB,
    256'h035F64C9_4DEF907A_59C5B475_DB2D4DDE_E65528DF_B5418D87_91A40518_626BFF09,
    256'h1F1BD0FB_AE67415F_DCA0E742_27478F3A_0D0E78F4_F82AE004_FB322A9D_35FFFAE3
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h5C5A9111_82B708E4_164E9875_CFA2F889,
    256'hD95FED29_36E47D0C_B80F48FB_051537F2_5C1AB82C_9E6681F0_F671BED7_A88DBC83
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hF4E13B0C,
    256'hA88B5A2E_A38DA2B1_B9D78968_BBCC29D9_A9B33196_D98B9EA0_DD8511D5_894D8150
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h377DE63B_FC0D2896_085EA8C4_170093C0_86FBA448_2F0258ED_7AC7AC6D_F4BD04E8,
    256'hF6CB5D43_11F278FE_3D0CA503_EF71AF31_0FDEF05C_6934D0A7_ADD15AF5_2DE1D28B,
    256'h1AC3A6BC_BEF7E0EE_76CF2E26_2244A979_522C904A_FA94CD2A_8C8DF84B_D946D57B,
    256'h6A8924A0_5BE7D4BF_1D8EB270_FF8F124E_CE6FC972_61AE4184_256C4723_05872B56,
    256'h77650B62_8AB13950_CC4C459B_E409ECB8_0E59DD42_3F8085C6_7FDA57B7_F37E1B30,
    256'h4FCA3E06_6E38BA9A_4955A395_5133B981_C8918315_DF66AA01_E9073A21_F1107463,
    256'h5460C5A1_0AB5C275_4D1635D3_C1BBAB9E_A220F9EA_B073149C_D7B37C13_D63299DB,
    256'h18889798_B4532968_1CE26B92_19E31EEB_5FD83C9D_FD36DCB6_679FE527_82401F64
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h1647_03A9A507_2D2BD366_378259B0_53132313_125568CC,
    256'h327C6799_DA0B4BA0_42253819_0A4E0DA6_2C0AA0E6_AEB01E6A_54A59D7A_3FB6A800,
    256'hCFD8DD1E_8766514F_C4B0E170_48567775_9A0D6148_4858101E_7BB4478B_F5251546,
    256'h5C9BD660_2A79544E_903836B0_5BE7555B_D4CC6A3B_1C9DAEE1_C9A662BB_855EAAF4,
    256'h4AD400F4_138C49C5_48382165_96B8A903_E945561D_8526A618_182D7065_994660E8,
    256'h1192620F_41E90942_B746E0E2_E7E9D17C_CB511B07_02AFF1F4_CE640B97_48D5C0E4,
    256'h74A10C89_73DA1535_E63CD58D_77963C46_A8F42D2F_01496F5B_D14504AA_4840AAAA,
    256'h178689A6_E351F857_6DC0CFF3_E273FA80_B20009D0_297A6C72_52823CA2_190E49A3,
    256'h4CB0379E_C89F0D68_A4D88B4C_88BE4915_C162E559_6E2B0101_4B0B81C6_340139DB,
    256'h2F8445F3_76844FB1_60ACA248_7AE8860D_20338B72_B4CB1150_46BCA7DD_921C206E,
    256'h8D7F7D87_50EC9844_90C4E3B0_30B03754_E1D03F0C_4853C5F7_E113A641_415E084A,
    256'h817B53BD_E47B9E46_5011E97D_6DF4E193_0B5CB1DB_181E1769_014E4357_304C548E,
    256'h7D30B5D3_B56019E0_830D1D97_562CABC0_30631682_B656C05B_B331EC4B_A70E830D,
    256'h5BDDCAFA_52AC5C56_A4D96990_DC6C2547_D2355A9C_ED3C8414_132BECD4_5B88DE11
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h929DBC5A_763E4760_0489CFCB_C522DFCA
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h36E37194_C1678B18
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hF7D74A89_4097D558
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h93B5B027_D4D9F23B_462A211C_E8B9F76E,
    256'h6D102217_6881A48E_A7345F17_1AC2036E_55FEC0EA_F8DBD81D_43F505EB_B2325E17
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hA96CCE1C_3E320775_C054EFE6_4069FB4E_5AE54712
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h562CF932_293BE920_A81E2AE7_731219D5_A7A572C7_83A97A8C_8E6D77F7_7C2BAACD
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h64C21ECA_0BD3154B_39125E1F_6647C961_85C1600D_8D865ABC_4CA84A8A_2CBEA8A3
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h9C1E1847_7DA86D06_2559B184_4F929701_63307A9B_5EC9D644_910F3D1A_E9BCAB1F
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h2422978D_E2C52CD7_461440BB_3FD34153_45DD0C8D_09896ED8_422BA337_58AA6DF5
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h82975653_71F253FA_96CE0026_B1BFD9A2_7B0FE7F4_4B5C5E13_63B103CD_30EDF7AD
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hB1F56D76_67869E1C_5FF8A46D_0DD621B4_9056AD9A_11BA26E3_F2499821_8A7728B7
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h1EEF7249_1036C3CF_8E06C0B0_0A00B072_6FF1E612_24732AF9_17E915BC_8DF507B0
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h4C248A87_27515C7B_A339A3D4_7CBCE25F,
    256'hE09B9D81_4AB6DB9C_ED9C7954_983187ED_EA2CB6E6_81F82EB5_8734815F_C2E02125
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h0FD2D1D2_4795F9E1_8E2A393D_C9BC3729,
    256'hC9A1AFA2_8E1EA177_C9121EC4_57EBB486_84F91D09_0461014E_7DF0B4A8_7CD5710E
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD86C733B_AD9A3A33_6FFC69F9_C511F04D
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h033490C8_0C6FD044_7E5B5C74_E55B46E1
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h02A86F2A_CFF76372
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h5FAC8C79_13A5A09A_529E11D6_6EA52D16,
    256'hEE4AFB69_812F1AD3_FE262CEF_43DAF15D_4DE24702_8C60EF65_F404C08F_60CF701D
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hA14AF022_5E497BB7_178D82A9_DAF75787
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h6D328F08_FEED181F_F4D6F018_A8AD6496
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'h0E9C6C86_748E75E4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'hB30AC873_A6B7BB50_FE3D8A9F_53CE2636,
    256'h4BE31F34_9B184A29_D208B25C_B396F512_89167EF9_D953197B_F06D4C08_42750C65
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h16AE90ED_ACDF5436
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h3D7CF8F2_413DD6C6_C741F00A_11E4D93F
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h671D062D_2ED853B1
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h23AB29AF_F6687AF1_764CE972_E5B8A4B7
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h97ECAC3F
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hF6882A67_B869B677_B1438FF9_692D1003_8B7A8533
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h746C841B_723BDEE1_534FD814_49DBE40F
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h7E54A9A0_90F074CC
  };

endpackage : top_darjeeling_rnd_cnst_pkg
