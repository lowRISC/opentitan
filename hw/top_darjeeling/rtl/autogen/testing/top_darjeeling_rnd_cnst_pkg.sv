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
    40'h48_41C90EA8
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h1468_4A625653_2DB21F08_435D40F4_574A2383_91651A99_58CC2671_DC781020
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h82D9D465_3DE5A528_8E14D20D_64D95E54_C5B57D5F_E61F96E6_C540D47A_3C4757EC
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
    128'h8A8986B0_8FCB77D0_831159F3_250B8134
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h49C66DCB_B021F7A9_2CF5C0C6_AE053B99
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h5562D7FC_AF6DDCA6_2003655C_EB43F3E8
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h42F268FB_E26BDA6F_7FB2D7F5_C5A0BC44
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hA9AE1E09_4D11EB4C_E4297A9B_8EA751D5
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h730C8523_7AB633C2_7080416F_BCBCA04B_C1FE5D40_87C45F75_5D6824EC_5D5E4874,
    256'h2DD52E43_4B64D69E_2E2FF6AD_2C726FF1_AEC6468A_27E6FBA3_20393413_5D0EEC1A,
    256'h8769C1E2_2FFBC6D0_CEE9597B_AF791F6E_D7367FF7_E8869207_ED071BD7_BD883D2D,
    256'h8A3E9D0C_7E4A8F78_EEA3DF9D_86C2ADE7_5496E8F5_43D0910A_1137F974_98FBEA5B
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hE6C6DB05
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h6E0C5FAC_5D85F899_E424F522_FD0EA861_DDBB480A
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h11EAC61C_ED49A326_F60E351E_B3342ACC
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'hC88DCA67_8158BD3A_986632CF_85B52E79
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h3A85A520_43BF04BF
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hB9954073_08D72F5E_77868588_EDF1E683,
    256'hE452C7C6_05AD36AA_F5BD2D2B_FEA59F23_86750B14_3F68B8CC_905EBE40_83A4C344
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h7C25830B_C60CFC3A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h1EF71169_3CDE0E3E_D616B290_7F057613,
    256'hAF8BAAC9_E2366482_FE86FDD6_477950FA_46878DFC_BA007460_82655EDC_8E640C4C
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hE6B81C94_42C007F7_8DA64A02_9B12101C,
    256'h37F5AAEF_4EC278B2_4D9E2CDF_E458CD4B_493DABFC_D05EF65A_35CC8466_D2755E8A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h591D67A1,
    256'h6D74DAF3_B57C9EA7_F9E35A4F_7CB5C928_C0A1A9FE_5D3879C3_23C72ED4_347A075A
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h67548724_393C1918_84301461_9C0C596C_970B3F1D_38969E7B_570E4E1C_98419116,
    256'h53608C31_88715A51_778B9004_805C3D26_368E8F45_6E2F6D63_102D3E86_6572529B,
    256'h69152112_48054C7E_1E7A2932_374F473B_79079A20_009F3335_1B025B92_76220D4B,
    256'h402C2B06_1F589462_7C43561A_8A894473_6A780A5F_467F4A13_55015023_0882426F,
    256'h093A9D49_707D2725_5D758566_030F176B_4D952834_64835E81_99748D93_2E68112A
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h0F710414,
    256'hCE5DEA1A_1A072DC4_AB7BA0EF_929D5FFE_85FF7E87_47F1A7D6_17AC1C0E_61C42612
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h5DCBD894_221C2280,
    256'hBE977D4F_C64D5A96_8CCA852A_13673731_D6128124_71437183_40CDB218_1D1364B7,
    256'h4B605B38_5D151308_C8AC8BDE_380D035D_2E01A71C_6919BB98_3B014A5B_A5AFB069,
    256'h581D8DC6_6A32914E_84856220_E92868C3_DEE26961_F009FC04_560AEE1E_86D75111,
    256'hC514AF3A_4194188E_1A75B03C_8109F586_A4999AD8_AA2E1803_3E2B3D24_2939FF86,
    256'h089354B5_5BCE0428_A05AC2DA_A50B11DB_55084675_4949D030_96E6DA34_7B846FF7,
    256'hB9901E6C_9442573B_AF80B317_37D13723_0CAEA3E2_41BF28E9_10F119B9_2C05FD40,
    256'h9816362D_969FCD83_909D70D4_437A3152_E9603AA2_31617565_A29EA152_F0715843,
    256'h776B1BAC_5F05EE49_9C958436_A07E8AFA_92DA9910_F0A98825_DD76802E_415145E8,
    256'hE8094390_71677EE2_CA027EBF_9894A40D_57AEC8DA_4A445089_D8FEB54F_391282AC,
    256'hC74ABAF5_0F417234_57194DD9_DE886E91_D88C985B_68791517_55D3647D_556F63BB,
    256'h3E842C48_41308C1D_D269F05B_41A48C10_AD9C2AA9_0DF4662D_1890858F_6B0C7CAE,
    256'hC3E5C9AE_81735925_75E98352_20ADF767_19710821_318C0B95_DD54DE03_5DB9A7EB,
    256'h24C8314B_D69C1640_9BD3A6A6_2A964813_2241536B_8705C480_11251595_BED511D9,
    256'hAB4CD720_9C688DE4_66B0CD49_20E9A69E_100AB676_0F38835C_41E17AA3_0030CA70,
    256'h8DBC06FA_B22DC899_1E138826_E1E43126_E73D1B98_851B861D_AFECD974_C97AE381,
    256'h0C50BA81_BBF0D494_47D4BAED_C2258C0A_7536AF07_C80F09AB_E1B02497_A4D93093,
    256'h0E804404_20218CEA_64BB08D9_AC4D8C1C_D0012E33_079A1B16_79202142_5718B9CE,
    256'h7589B659_47A170B0_1E13DAF4_4818F125_4816A16D_F6F8A78D_661432FD_8D179609,
    256'hAA639CA8_6AB9C787_F8E9397F_49AA0E29_1050738E_6C0FAF92_A5F99C59_F6F00614,
    256'hDE671C1D_04CC13AC_9E7C6D21_B956A181_AA698AC4_6565F92C_7B04994F_0B8B6F13,
    256'h083FB6ED_7C2A68A6_14F1D419_C38A243B_098599E0_A2AD82CC_B02D3CA9_968605DE,
    256'h764EC94A_0CAAC997_9CBEB294_74F9B73E_8188FE55_BC9D47D8_38738099_8C8E99C6,
    256'h6396B502_2AC16AC3_3421C5C0_7293DC98_E5156EED_49951859_0A82497C_68ECC810,
    256'hA64ED870_DB0D7CF1_4349B377_09BB66DE_9987C5A8_45522784_860A1657_8C586180,
    256'h9AE02976_74D27700_9C412891_F93F6111_A346E3AB_DD0530F8_4AC9F23D_E55CD911,
    256'h7AEF81A8_E20D467E_293A3E6A_190964A2_C42DAE85_B058A2A1_0A6D3505_109B4F06,
    256'h529D8BD9_8319CB24_095CBDD5_F866A56B_5ED84E01_C0DA6820_07000BA5_C5D26A0C,
    256'h33B56EBA_E8B17ED6_2E627B2D_16542C2C_6815154E_A881541A_AA86C715_3C432245,
    256'h85AD2542_CC294C40_38F0F9B4_209525E8_B1AB778A_F49EEC76_9EA797C6_D3D44F2F,
    256'hD8F3BE94_77DB4B61_253C1419_2D203DA4_71ACB435_92322CD3_3981F373_07A71CB4,
    256'hE1667BF0_0005DBB7_534884FD_56C6F88A_EEAF08A4_DDFE3EF1_D940C721_E2E5F4FF
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h90F7EB17,
    256'hC34EEAB2_CB486586_73C5090F_D03A6691_079F269A_2C4E75E0_1B250EDA_1845A3BA,
    256'h41613CFF_3EDBF802_D571E7CE_403175D2_9C862684_1DA83199_54BAC164_D043F0E2,
    256'hDB0EED7D_C7ACC05B_042A3B0D_84089FF2_C44E2D76_78924D4F_A99F1120_C5235AF1
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h1F74943C_68033614_42CE4B85_F28796FF,
    256'hE38A9E69_40CAC71A_BC441D7D_7C35A712_3A679D2D_F41253DA_22D8AF83_1B56AEE3
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h58D37B7D,
    256'hC8F5FC88_79822245_EAFED861_97812700_D8B2054A_4E2D7F43_F958574F_82C637C9
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h0FEB_F5D1A295_45AD86B3_3341BECA_7F59B2E7_654B8D22,
    256'h04207A06_6014F34B_0D6B23A7_4F86CDA3_6612C602_1489D8A6_516D843A_575DE064,
    256'hB207E571_C12D191E_41C8F11D_A0A09E4C_C1069052_ECDE0648_5BB5ABCC_4B14619C,
    256'h2A1E3215_B51268BC_7CFB4414_63C2E8D5_4086CC7E_A04D6705_7AE814EC_751A9CEA,
    256'h650D0548_9D8BC39B_D1D78B55_C21B8545_9D159921_6D5C3B9B_041B1094_C045A021,
    256'hA5CE8BE1_C6D99CEC_9FB3D7E5_37B6CD4E_0CB93D89_AF496C19_C6F25659_209DA581,
    256'hBD0C846E_44826220_C9394E60_3F205F48_CD46E3BC_452C72AA_C351090D_1889014D,
    256'hBE46180A_C25EBA4F_A62C4B22_5033DA50_7D71861D_C9CADB5D_7C2C454D_5504C5E5,
    256'h010C8D8F_98182853_0B248E66_0F978243_92585688_0B655698_46466AAA_D3703B9B,
    256'h51C8C3D2_A704C739_29692339_8954A4AC_03DF2104_A24822E7_6F6ED1E5_7558CA52,
    256'h5C043AD9_00AEB630_A02D3F7B_AE01AA20_798D614A_18B3E657_2605A968_2439CF08,
    256'hA41A6CBD_E09383BE_8FCA70F3_E0E8D2A2_C9AFE5A3_C391E6D3_7AA4540E_29C44A1B,
    256'h60732010_E90ABD98_B9421EDB_89C019EC_E5463A49_5B006848_A46DBF0F_312FEEA3,
    256'h8159F028_17AB5B6F_11C8644D_E576A93F_E449A858_0026E9B5_C565577A_A20D7B34
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h9F51C919_58ED127A_8C79AB81_A2B13AFC_144FB40D_594DB231_99DFAC77_55A70CB7,
    256'h3B8BAD60_5C701088_92E2EEC4_5DB6B394_F127E6F5_B8C6412E_6BCD7E95_FFA4BC50,
    256'hF929A67C_DA98339C_9E62A54E_203ED9BA_F848AE47_9A0666D5_C5FE1EAA_2638B523,
    256'h36ECA965_C339E891_89F3A01C_8AFA1B11_80453D40_4B53A344_6ACB2F68_16D11D2D,
    256'hEBD32B25_15E30004_DCBF6778_074CFBBB_EFCC42F4_AF74866C_0E96D79D_1F18C78F,
    256'h326D8757_D4D2177B_495E224A_A171908E_0BBED83F_24F7525F_F005E785_0A342830,
    256'h2CC8FD56_0184EADB_5A356ED6_7661F697_C2CAE0D0_82B99BE9_3CC16908_54B07D37,
    256'hE4937309_8D1A0FDE_BD647F43_13C021F2_83CEDD03_757263CF_2A6FA802_E1465BE5
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h0743_142C7098_B9511068_4852F13E_143FD81D_6369FAED,
    256'h2A94051F_AF975A72_B6473151_8A9F4D43_5CD6DF4A_164959C0_4B1CF004_E3340993,
    256'h656B4BFA_740E2F2D_5D5119B3_94D35252_A09202D1_D16A9617_05CAADAA_7A8A664D,
    256'h50612A1C_28867BC4_C01E9F38_A0D38474_9CE36663_4A480D39_71C08B18_2084B00B,
    256'hDBB87492_151E3465_B835C194_A9841597_666E736C_C1428B7F_845B06FB_85055C34,
    256'h8CA98B36_8A283645_7D0FD62A_B48648FE_A8552BAC_ABA317B1_F5896743_DAC41530,
    256'h3A740A51_24406571_23E2285F_288D8F88_50EAE2C0_C21647D9_61F4D815_7C878252,
    256'h5A84833A_7AADE11F_864563CB_700B9122_F213CB1B_33D5A492_98670198_D0100044,
    256'h15F3576B_C0EB7395_7A584425_29B81838_1491AA38_817DCBE1_0586EA5E_C57E1E83,
    256'h06F1D6F0_69194059_9E8335E6_63DE2CE9_51484B93_2ACD5AF2_3225149B_600B75E9,
    256'hCC5B6E1C_972C75F5_DAC81064_2A9DD462_81D5DAE8_42B0C1EF_CB9DED8A_DF44A72B,
    256'h46665DC6_C337263F_562351DA_4EF16CA3_9394006A_1A6A0907_2786DAB7_F3B5D0F6,
    256'hBA84B362_EF832071_DE9E372F_E92C0899_1DE6399D_9DDAC447_A17DA029_1708C60A,
    256'hC3C45235_20231E61_AD2430A2_84DA883B_26821650_60E68D25_84D6C097_A934D8A9
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hD1EDA453_59BC7337_84733101_DEFE510D
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h2F22288D_545F314C
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h8D3FACDD_AA9193FF
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hE971C21B_C1195568_A1E14968_F6470E2A,
    256'hD3F37E9C_52ECC9E0_17027461_142FFAE6_C1D8B37F_B1DADADD_E0D3CA6E_6A2358C0
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hCC26175C_189599AD_8BA63B47_422F8FAC_51EF9549
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h0E1D28BA_99DCE506_FC589BE1_DE2D8AB7_AC514576_1EEC8245_451D88E2_92D0B0D1
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hB10882A6_92C83463_9F678325_EEA43947_62042104_04C00B6F_6EFA3997_E2B24E53
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hC492179F_E8105AC4_42A5EBC0_F3D85163_644ADA34_07543C75_421F2AAD_F4C0892E
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h3F7B3784_405243A4_AA4FB897_0DF6E0F7_8B643410_259E59CD_A4FC00E7_ED67286F
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h31075261_8844D2F8_1C19255F_E753B799_5CCB8A2E_EC70F227_45C139DB_09B25B0F
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hEDC9F61C_67905E31_CC3F1003_D7AB6375_B104A463_1FD6E1F9_A5CACEA4_85646E64
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'h5F99C7D1_B6D15DF8_79CF3595_9C426CB9_4046BA8D_481EC885_4002A81E_9142AF6F
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h4979CBF7_FA885B54_E5A54309_2670635E_FDAC158C_87448973_1AAFF596_844A2255
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h800FECC4_2EEB5B04_60F67AE2_FF4389C0,
    256'hD614C4EA_2C7AB818_8EDF8197_D16AFAB1_A92765D1_3B89FB9F_B19038E9_2F8A0B47
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h9DA25FD6_F656F66D_F89F4D9A_A5BE606B,
    256'hEDFB0C84_F34C979B_616815CE_F2C4EF6F_019905CF_0F143E16_90769CDE_173DE894
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hDE60F751_39BD9EC0_81E92D13_65795B31
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h2F309877_931A933F_69487E3E_530377D8
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hF6A201FD_6631C98F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hF5C8C1A5_BA2C2715_39FF388B_19E427F8,
    256'h21FABCDD_F67454D7_0D6A9FBB_58514B89_663CA23B_6B2D2432_D02B1186_70560F0E
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hF8982BA2_DD7868AD_3369644A_F4165684
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hE6B8957A_B73FDCB8_0995B277_5BC9E457
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'h56CE3973_3A59B3B5
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h2D56AAB0_ED62D170_4243EA26_DA3B5B90,
    256'h621603C9_5E47D2B2_26B13FC7_BEA148F5_1DBB8C39_60C7E7BD_3DE965C8_031C5CCD
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hF80E2349_2F2E858E
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h79761BD2_E0C0DD52_6D906F37_171E38F5
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h809CA85D_4BE0BCB3
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h26AF7A8A_39C0ABAB_0C85B5E8_378D2A11
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h3C064F5A
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hB08F3CD4_782B49ED_FE574C60_1531DC7E_8CB07688
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'hAECC58C0_A236C6DC_FF993B5A_4D777088
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hBBDEC26E_61FFA526
  };

endpackage : top_darjeeling_rnd_cnst_pkg
