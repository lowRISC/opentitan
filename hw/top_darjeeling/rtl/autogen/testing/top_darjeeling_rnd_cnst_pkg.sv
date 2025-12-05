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
    40'hA1_C8EF1830
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h3569_628C3719_48E0086C_13E45C24_1428C193_8452DE9D_16951181_E67DD809
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hD6780626_A12B5904_A9B37439_F8177D19_D04D3FAD_040ED029_09A9EA4B_5429B9E6
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
  parameter logic [163839:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'hD08F694A5F790581D728BD369D03F8087A60A7F8ED956442C9CFF0F99E594C7307F376E7B2B2FF8C,
      384'h6149B9FF4F5979607AEAD63A44F896431DF745A52C5AF5FDF86D2CE9FA1041C43F145A8BF5BE7640D7AAF2481067180F
    }),
    384'({
      64'h0,
      64'hF29E32E9E581EE74,
      256'h9C47222C695C123916E90F1BDDE834C31D3EEF689E998822EDDEB20732F666FA
    }),
    1024'({
      64'h0,
      64'h18E89A42A1CBF7CC,
      256'h276D9C42B4B5C6539C73A2705A4682BAA1885457797963C3980BFF063FC8BC64,
      256'h2E2904AA8A7090712CF9A372BE9C2B9C1FBFF3B68368C5AFEDCDEE44F5D8D84,
      256'h4C8FD64171EDB20835AEF32CF20B0C620E9AF6C53593DAEC8E3CAA2E495A8976,
      128'hEFF32B59C0A86294D9767FDCB4745699
    }),
    256'({
      64'h0,
      64'h506068E7D20C8309,
      128'h2552A6AA7830346413591B15ED255318
    }),
    384'({
      64'h0,
      64'hBA37DEB973D827E0,
      128'hB5742826D2CE8D8BB874DDD1DBCA5322,
      128'h1FB5110B0618183CBF722F142EF9FACF
    }),
    448'({
      64'h0,
      64'h5A7F3E2373A78AA2,
      32'h0, // unallocated space
      256'hE78E601C1704C34A6DFD043E96E1EF76D15C0798EF406091D605165216FD3F85,
      32'h0
    }),
    192'({
      64'h0,
      64'h8688686A7D26F94A,
      48'h0, // unallocated space
      8'h69,
      8'h69
    }),
    384'({
      64'h0,
      64'hDDF650F1A00008EE,
      256'h58B183F3D37975B4A9524DE21084A9D64BBA835C10B5E29043022273F7AFBF68
    }),
    19200'({
      64'h0,
      19136'h0
    }),
    33856'({
      64'h1F2A6BD606D55F72,
      30720'h0,
      3072'h0
    }),
    3136'({
      64'h6FB88C3B4FD535BD,
      1024'h0,
      2048'h0
    }),
    65664'({
      64'h0,
      64'hCA832DA13EB53FEA,
      65536'h0
    }),
    8256'({
      64'h0,
      8192'h0
    }),
    1280'({
      64'h0,
      64'h28B1AE331BF3824C,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    1280'({
      64'h0,
      64'hEBAA1ACD79D438BB,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    1280'({
      64'h0,
      64'h8A4FE08CE276C9C9,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    1280'({
      64'h0,
      64'hB5A6FD9823EB9F1C,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    1280'({
      64'h0,
      64'hB51350C5C23EBE77,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    1280'({
      64'h0,
      64'hFDEEF22E74536D01,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    2432'({
      64'h0,
      64'h4BEDD6920E68A84C,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    2880'({
      64'h0,
      64'hF9D303313B0977A8,
      512'h0,
      512'h0,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0,
      512'h0,
      32'h0,
      32'h0
    }),
    6400'({
      64'h0,
      64'hC167C84BFDB86457,
      128'h0,
      6144'h0
    }),
    448'({
      64'h0,
      128'h0,
      128'h0,
      128'h0
    }),
    7744'({
      64'h0,
      64'h2A24E15352C559FD,
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
      6304'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    1792'({
      64'h0,
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
      32'h69696969,
      32'h69696969,
      32'h69696969,
      32'h0,
      992'h0
    }),
    576'({
      64'h0,
      64'h45515694E825B33,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h0D20B077_21F7FF50_7AD2B9FB_9CC7FF06
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hE4C72C47_D9E15FA8_FF9F8283_3E32C151
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hD2FD2987_E3062F61_19C7560A_CBBE9F6F
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hFFC2171A_49199BB5_3D8E0DAA_8F0578DB
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hAA5F0227_91480B4E_709E0F80_976E0966
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h01357E13_758A3E22_11E20FAA_36D00779_EB2CFF38_B90ADF94_A0675DA2_63541C78,
    256'hAA9DC0C6_23C09EE7_FD16A668_7D3A1B4E_21456518_EA00DB8F_75489D93_2535FCB7,
    256'h684ED330_AD9AA219_EA28BFB6_FDA16A61_BBEACDDC_92216985_8A90A977_C043EB40,
    256'h7A704254_4EF79B15_F8DBE994_6ED90ADA_FCCEDC18_C38AE447_3E404D38_A4D2302A
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h295C50F4
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hCA09B9E2_22B820CE_D83F7979_E4E9C395_2A6534EB
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hD6C33DCD_8C46C818_0DA77F58_394513F2
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hABB1B374_4276549A_FD120E86_2D3419D9
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'hCCFB691A_3E5D0916
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'h0DE14097_A1D4C397_D0AF43CA_4A7BB159,
    256'h7BDAA5BD_7822AB7B_44D54B87_DF2291D0_A0DC1A19_9BF4EC73_224ECC41_BE8F660C
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hB852739D_C155FEC8
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hB43A6878_187C6372_714364FB_CCB31F29,
    256'hDE201061_5C1E636F_6633B90B_5522EACF_67FDB008_3D7C1AD1_25A5551F_AB932AAE
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hE67DC054_48A1A0AF_54E3245E_8C3FDB3D,
    256'h731D4C7B_C5218650_27E19AEA_CC768260_6BCFCC02_48BA5F3A_591CAB5B_6EED6374
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hB80B1581,
    256'hBA47B081_EDAD7956_48590976_8EF3DBA8_08CBC6D5_7FE7489F_41549870_395C90D9
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h842E7064_1D6B4C9D_696C0903_8062541C_1B523146_0B4F1F85_8F203A0A_22137A3B,
    256'h253F872B_2753245F_0267379F_7E639C2F_953D3565_689B1A32_49734507_365E6A08,
    256'h7D42342A_7983238B_764A1898_9916217F_93611740_4B304E66_77780C48_29929A71,
    256'h158C8110_8E0E9012_59387405_5D0F6E19_44049E14_56338D4D_72573E8A_967B4188,
    256'h6D91016F_26947500_110D8982_43505C58_7C475A2C_2D862855_6039511E_063C975B
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hD09377DF,
    256'h413B2B19_12721612_13B80315_A177C751_6ECD4B00_2AF6B492_53AD7151_C8E8F1A5
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hBE81CBD1_3E35B1E8,
    256'hC41583E5_CA828487_0362F987_35253BF1_7D9AAE9B_01932EA9_F6D4D820_0DCA924B,
    256'h89AEB3FC_6E946FF2_8263228A_DAFEC52A_2B884EA9_0F27C0E5_83AC5B40_C010734B,
    256'h1275AC32_DF811EC2_C5432829_A50EE8C2_51E3B3E5_2C4A3B69_81B88219_83718877,
    256'h05454408_CDDD6C71_79820470_A074AC44_758B66A5_5B5C6EC7_FAAC75C7_1A452967,
    256'hCEC2B25A_2AA98349_9E9AC241_F89A3341_36B94F23_E36A54B0_00DAFC30_D93223E2,
    256'h7205715F_B63E7F7E_9C44722D_47E433FA_F501C7A0_D21586DB_A3D8FC42_8A413D21,
    256'hB5EC9448_6D616175_7459A413_54588DB9_E6107C3A_33DD450D_B30BD968_BC937882,
    256'h8346838A_0BD634C7_1ECABAA1_949E8B23_11F47BCA_54B08441_E9326319_72445181,
    256'h64AC8B56_C22E3D46_B2E19949_6DF91A6D_5027116A_016C9A23_89ECC39D_855C49A6,
    256'h8545AC2A_6E083A9D_2E60AFE9_05E8B04C_24893117_5743BE21_7320C43E_18564D50,
    256'hB4A682ED_E600A1A6_DC16F71B_2ECCC80D_728884BA_3920C3D0_35A1C8B3_55362AE3,
    256'h199DF4A8_5005ADB3_B8A3AB80_849DCF97_55E8DD7F_7D85CBC8_65941021_546A6A97,
    256'hCC085E42_1349DEED_895C358A_7438DA39_9DE63A46_F05270AD_D47B3259_C407D16D,
    256'h107CE1E4_346C374F_23DE490D_41D09872_519148F5_5A66E693_24863A2D_A342C6A5,
    256'h09737D00_809ED065_4EB38522_67040495_CA49AD59_6AA35C87_2E64E530_DB31532A,
    256'hD952961E_005C22BA_21A23A99_2043F2FD_6A2A41AB_13137007_74245F3C_5A7105B6,
    256'hAE9773EE_A56A2348_E1FC9F96_0AAC059A_1419CA57_68288792_A272D928_44624E67,
    256'h81E43D66_A756048B_8E40B745_CE28864A_2D79BA9E_A3D151A1_4F345D95_A8697381,
    256'h42C69041_8E6CACD4_AB751D4E_82BAB558_1A089C25_BF74DD22_DDEB6AE2_C908E193,
    256'h2EE97F0B_612733A8_0E83A3A1_D6BE4622_44FD7339_1195D9A4_4CC8C5B0_74B28965,
    256'hD456C28C_A8F2765E_11A2444C_8ADEEB91_F76869E7_A598301D_0B95385A_58B03CE5,
    256'h00A4747B_16242DC2_21018203_37D55F92_96D46D66_136D23C2_64841912_BDDEB460,
    256'h9AE5F10D_EE6BC470_88C38524_11B4C7C7_64A7934D_31E31D0C_54BA02D0_4C0ED001,
    256'h54A3CF94_46B5A289_536806B8_A823AE2A_16163958_820B2A60_8186AC13_CB0D2F00,
    256'h6B401189_4B6E089F_1F914C66_F8F86322_9A1D28A2_4239E706_96D3B19D_7009666B,
    256'h63088CB0_110CC149_A55C0216_3E9DC784_3E640420_7AC7BE6C_81D90C44_C4A0B956,
    256'hC0C69419_B9439557_C80DBBC2_737A14C7_009032F8_B65B714D_5093D450_2A812CED,
    256'h43F50579_6651CE96_26EBC978_570A6AFA_F707729F_0214C367_1C6A196F_121C7491,
    256'h377E6D5B_589E9104_E2F13D87_F11520E6_5F9235BA_4079E9C6_76F3585B_C9217BB2,
    256'hD8E119FD_BF57A42E_F79EC9FA_366E536E_1C3654BD_A6F768E7_81944338_619F5D57,
    256'h6D888FE6_28D630A8_D9759C21_C51BB248_51062BBB_C0AE801F_FBEE9D4D_8B48487F
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hA842CCDF,
    256'h4B2EC9D2_8B150F71_0414CE5D_EA1A1A07_2DC4AB7B_A0EF929D_5FFE85FF_7E8747F1,
    256'hA7D617AC_1C0E61C4_2612F0F1_FA533FE0_5F758B96_21FE31C4_C8719432_8BAC3EFD,
    256'h7F8F4DE7_2295AF15_BB8788A9_1BE7E977_56C83F7C_886F4D03_CB27B76F_F5B776E1
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h9827E164_4CCFDE85_50779FE0_5236BDCB,
    256'h52B8EFC2_6E1DBE98_1AD2E2A9_2BEC3819_CC364D88_A57F854E_B5B47919_710F0700
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hF463EF2F_DFF5F6DD_DC13ECC2_583D51FE_DB1B6197_DCBB40DE_C2A9FE69_FAB1EB9E
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hE13C3678_95ADEFD6_DBB19E7A_24526B82
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h5BB435ED_63D9513E
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h488F3FFA_7700EC4C
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h8DF69CD7_1B07313B_F8070A19_F1492984,
    256'hA5EE7449_FD9A0E90_3858ADA8_603FCC85_74DF6589_7986F23E_B0E52FE0_91E4DED2
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hB70FADC4_5465678F_050F9100_557F374C_1C36F4CB
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h7B416B49_B114F994_A969864A_57C3482A_B3BDCBD9_FE825728_F7BA40A2_2C9719C5
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hD7C160F4_92D0E875_7631EBF7_52A1E560_4E2D6171_F5DBA9EC_4249052D_CC7A4D58
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h4D57AC27_843EA2A0_163EFEDA_5B24D93F_97D62D99_C960542F_4A1F2595_192E9A96
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h9A885419_A9D57E36_519FA42D_20EFA348_CB77F508_9A8381B6_2D9717B3_647E5CE0
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h796CA68A_A29523D3_F94F27C7_4ACAE76B_3E145326_741F804E_3C3A3451_469C6118
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hFA23BC32_E428AD2B_E2584FE8_D5491FA8_E7F19AAA_4133AD0D_2704702A_E2FF9D98
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h49FCB598_74CDDC9C_BC645D9E_02A96B99_80911844_D3C74DE8_5E05164B_829D484B
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hD447C9D7_611999CA_523B1157_5A82D625,
    256'hEA331F0D_D07B9876_A95D4846_9D8BE58D_526100D8_26EBF413_7728E993_B979B05B
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hDDC26CCB_34AAB934_13F8B7DC_7CC8C4BF,
    256'hDB394D03_E99A0DAE_61EAF3B6_4EFFA6DE_29A9812F_FD69DD7A_95A3E3C9_9E381A97
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h68C85F00_2483AAFA_2A1B591A_4617B8F7
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hE2806138_001D6EC3_45718E6E_7248D8D8
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h5F141C91_5C06870E
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h1DB66B08_CFE8D13F_76590967_B339B779,
    256'h53DF7790_C1D57A63_BD4108AA_1B8660E8_0B27CE30_03EE9C49_AEC5911C_6D8B228D
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hDEAEB4EE_A0BA96FF_2B3EB56D_EBDBC1B3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hB6ED4DAF_88E9EA4F_8051D088_092FB879
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'hFFD7E826_5FAF402C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h112D94A4_693327D9_66CBE2CD_E270F0AC,
    256'h5BAD1F7D_686EA5D1_66C0957B_1300213F_D0ED671A_63AD1F74_13A284AF_0F839BE3
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h0A553E45_BAB60FD5
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h30AE8415_6D37CC68_063276F9_E85FAEE1
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h29AE80F5_B440DC77
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h9649127E_C56C7B0E_9645BF23_1B5B37B8
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hC5559AEE
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h3AC76437_9B540182_4B549F99_1766E911_9F5E97E1
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h8AFD1F07_532671EB_83C820E1_F1EAA3A1
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h8AD34D47_1B199CFD
  };

endpackage : top_darjeeling_rnd_cnst_pkg
