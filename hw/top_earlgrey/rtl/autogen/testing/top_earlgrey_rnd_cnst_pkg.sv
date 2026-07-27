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
    40'h08_F9EED04C
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h9577_622D2367_4E16822A_46C638C2_5664F143_44750422_379C01F6_10566801
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h956C7F90_4B9EDED0_9B89A754_33566F49_63D9DC27_F3ECB11C_E3B87AAA_7ABC8592
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
    128'h0B188108_3AFF7BDE_18EACFF8_5679453D
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hA77D92A1_76B87118_AF11CDBE_78D67060
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h615A20B9_C0740F07_969CCD2D_10A1A6E7
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h988FA528_AC032E0A_6138CB83_16FF95C6
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h5CD7A1A7_68B06E01_06D60EDA_0F1BC67A
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hDF85BD9A_56EA088D_33FFAA6A_1155AFB0_169AB2DE_3973D027_EE30B8F9_01F644EC,
    256'h7CD3E56C_8ED1EC38_739F1D0D_EB7C7741_99CF6DD0_57F44C13_E25C7A58_77BC5242,
    256'hE6EE63EC_DF458AE6_596E87F9_F973DB98_AAA29356_8FD1F31A_0165939D_819D1518,
    256'h690E6473_CDB24793_91635057_CA1045B9_E1917E1F_F0189B04_A4F7FBA9_60FE098A
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h4FB9D469
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h769F9B6F_A88170B2_0267F53E_C8DDAAAF_1260C862
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hFC05041A_1B896350_C9636D68_14D23E2F
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h5FF1275E_F19959AA_A8B6A004_D5574984
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hDED1CC79_BD6787D6
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h76599773_2C42D6C6_D20EEB45_DE3F91AF,
    256'h4C07A8CA_1E7C4598_938050ED_43CDEBD8_674E22D5_D801BCBF_3809FCA6_88E69399
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hB12E1AF4_339E1F45_164A418E_BC52210D
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h58DC6550_8E869AF5_65C1B87D_687EE837
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hFC119F5B_BE7395CA_C38919C2_7006C23E_14259108_40042A75_ECC25D4E_2267E3BF,
    256'hF26E003A_ACBF7D51_3AEA01E9_EE420D5B_523F6B00_C81BDED7_282425B1_BB59B801
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    64'h481ED579_3ACCFB3A
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    128'hB869F014_42D0211E_544E5F2A_66948C77,
    256'h46A6EB8F_40C643D6_EE8B60DC_A2438A33_9EBD81EC_7D77356F_3095CB60_7F36B87E
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h3EAE3C2F_18B4666B
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h7DC306FB_5D82893B_03A5445E_87FC8A20,
    256'hDDEEF660_4EAABCD9_6B8C52BE_8E843F9F_1091D540_ED8C2380_7165B672_C96F4597
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h967BFC5C_0D074F65_B5742CEE_8DBADEF9,
    256'h8EF045C5_1ADD590F_F66A6C33_2A0BB432_621B97CE_4BFA8DC4_46602908_41EB8205
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hEF142E02,
    256'h83257145_13BFDC2A_062C2EB4_ECDC716A_92861FF7_C06C6910_E727CBED_4EE2B19E
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h64058194_3F434535_8388890F_78626692_4B904E13_2A5D1060_0C57399B_2E063B5C,
    256'h37002F4A_48179151_82538B27_6C2C635A_348F2455_748C8D3C_6F1E2380_22417504,
    256'h9C423386_56323A85_61976D31_7F2B1B38_0B307019_01287A84_0D651A07_694D9A12,
    256'h095F6716_4C9F0898_2D117C3E_54188E36_8A79460A_961F9D25_9944686A_1C4F875E,
    256'h93779E3D_0E495B7E_71031D26_14205950_7240157D_7B952902_7376586B_6E215247
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h9D9F58F7,
    256'h0432D8BF_8509A79C_A1D3AB83_A61AF330_C5CFD188_035E2F18_108133B3_8A7167F8
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h1730472D_BE79E723,
    256'h5E533D13_5B585590_45F55C9D_1D021955_3C5B2708_85C0B3CD_35C62D1E_CF7260D8,
    256'h7AEB26A5_DA341F11_C5F694A4_300D6B76_EDB13E3D_252F9632_A8A34D50_C01C4B84,
    256'hB502E7AC_70151A6A_C6C3130C_771BE1A9_DDB84B1C_E9FE0531_95B74C84_B4A6C284,
    256'h89096785_4A5653D9_645C676F_2BE71805_B7A71B3B_05761E28_A50C84ED_042A5B47,
    256'h168728BC_66E25531_116F5795_E1F7414E_7596F0C0_2AEA387E_7ED104F4_CAA1CD44,
    256'h9E35436F_23360E73_E2A42588_A268FC55_A836A28B_DF113C58_3A0F0A65_E648EA11,
    256'h5BDADC42_C14761F9_D1075160_AA88F30B_2A37867E_0FCFE8C1_CC6BB073_585224ED,
    256'h51CA6885_65D22F03_54EFB810_9F0057D2_D9C3480E_E3499211_1DD996EA_C201B5EA,
    256'hE66AB189_3AB3AE23_4B0E88A9_88545313_11C64880_0E704170_A43C1980_61BAC87A,
    256'h4DEAC2A9_3BD1F268_FA29D737_206BB028_46FD0F55_624A5960_306BB83E_61082ACC,
    256'h75823C9E_4408DD52_E198729F_7E9F25FC_A3B9131C_0A2733AC_5749FC38_8149B407,
    256'hB500285C_68010F00_26750BDF_9B28E8A6_AED821B7_A41EE910_B4534AE9_7E7A25A1,
    256'h4A90562E_17275986_36E930A2_01A64E68_027B808E_A78EF477_D9F099FD_A1AE3046,
    256'h12512FC2_65C9C191_25D70D6C_D9090943_C6712489_DC37C0DA_76C46500_B38CF823,
    256'h08D8E69E_2AA493A6_513B47D9_14B710AB_A526F875_44347AD7_4ED4E0E9_85C25B43,
    256'h72467E12_604D80A5_55A4D1B6_0B70C200_5A5A95DA_ADDE5880_C462185C_15E10717,
    256'hB75C24FE_E1BD4D10_6104B4D0_12446D5D_D9A0C937_AF1849DA_FF30AF15_D20C69A5,
    256'h051EE8A9_C9B7827D_68AA5666_3195EBF1_40C47C18_1BA64B62_52A88C35_2B4B07F9,
    256'hFFC3AAF6_78B39CEF_D5B47C0B_8B97A2DA_751C425E_DF8FD916_3A33541E_C661A73F,
    256'hCB108D87_B80B2C69_7C585258_DA3C3F4E_5C7816A2_E07B45F4_242CC0F8_4C302639,
    256'h30A61884_D0697B99_8D948C8F_C3E828F8_EC455B58_426BA51D_97B4BA59_DA304108,
    256'h63500981_6699E62B_72A0B62E_B07AF327_9CD889A5_93CCCBBC_A44E878B_0A482AD1,
    256'hA3D4FBA6_0835581D_324A057D_933208AB_BA8018C5_D1B2C92B_2B70DCEB_96A8A270,
    256'h27B66371_3A2E7CEB_505476A6_E1621A26_BEAF6419_EF690701_FE5CAD13_9B1C1F18,
    256'h1B058C45_001591AB_14C7E034_A569509B_163D030A_98A44CA9_B1A47798_0A8E0A8B,
    256'h8A7C46C4_9928CF71_52D8B291_C585B6E4_69966AA0_E05842D6_49611962_EB656024,
    256'h6CAAD064_796EAA13_86928BCE_4505D72B_D0E5514A_15C5E048_224FA1B6_EC614E20,
    256'h92FDEA3F_20B9E5D0_8C948121_360E62B4_BC3D0AD2_12055C28_A6F119D1_A71A0C70,
    256'hF90EC889_52BD5F9E_5834590D_26945A8C_878A5A15_95B2C730_D87520A8_14CD284A,
    256'hDF5BF895_5D8C714C_BD9B84A6_AD6EAE40_F6B2E523_9AF670C5_022CD0CC_511EA064,
    256'h923B6865_E71C8738_13087492_C2D322EE_971519D2_F8653DAE_C32C4090_24D544B5
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h3238DCDF,
    256'h7DE88B56_B405E02B_BFD73849_C511F7F0_B79F91DC_D1D589B4_CAC4372C_385F89D9,
    256'h02019DAB_B6DD5702_2C77EDE8_609C409D_905B3C78_19B26A67_43288199_28C5D79B,
    256'hF1DB63D1_1E1C31BB_C9A8C73F_C4CC3D14_CA6BC0B9_6812DE7C_775A54FF_19343CB3
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hFE376B54_463DE2A7_87383305_2CDC7C7E,
    256'hDE8F6F6C_0ACD6FA4_475A405E_51B27268_02528674_DEFED3E6_1B899E26_814AC408
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hE856F1D9,
    256'h08E3F70D_E343D222_6E9E8644_65A8EE55_EC0E6A29_6789DED5_C0AF59EE_62F1FD1B
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hB9330DB8_45B48936_B039A170_F15F724E_E2A65A14_1EEF3F7D_AE11C54D_FB2113D4,
    256'hB218D85C_83EE4A16_970E296C_9BAA79BF_D553C364_3EB34943_759881CD_EA730923,
    256'h479EF28B_27FA4B86_DA3B07A3_461B7F41_F99C2042_C7F7CF88_BA381234_0A625067,
    256'hDC1517BB_55A8DDB5_56D663ED_F5F61C19_5BECC4D0_E3FDC17B_8C0078DE_769DA226,
    256'h2DA5F891_DFCE1D6D_80AD6182_6E68102C_E8E93C74_7E3590D7_03C032BD_57F48466,
    256'h08E631CC_87FC6BB6_06D3AF96_8F3D02A4_9F2F8E24_0FDB2BA0_A7C6778D_6037302A,
    256'hC804F359_93928558_A9E09599_01CBCA4C_510C44C9_0BFE9A7A_C25469E4_28526A8A,
    256'h1FE5F048_6F407CE1_D2BC4FAB_D965255D_D13A711A_EBB72EE7_945EB105_22ACFFBE
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hD5A7E3B7_E444732A_39A69F03_F5A88525
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hA587CEDE_A90913BB
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hCE814E67_94DF2BDD
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h938856D2_94289EA0_B63DF8C7_109DF24E,
    256'hCF9428BE_B3F1C3AE_22533F65_DAD2343C_2D5D1EF1_698F4589_5BF57801_A005BE66
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hD13CC6A8_A03237D0_9FF8959F_0E6522A8_D7474677
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h9DA8413D_DA43FECD_D6C1A586_93232D1C_3E361D85_6AB2D1DC_6455D87F_13C9A467
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h1446BEA8_56D5FBB5_4BB5B253_A70BC372_CFC9BB0A_B38A5EDA_BEE7D224_D1A66837
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h8437DD24_797B602B_068C0A1A_ECA298C9_6A8130AB_336462CE_E1BF8C65_3FDE5A40
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA24DF78E_146916DC_55F8CE6D_BFAAD089_10FBE182_2C22A17A_376FA131_5C0CB3C2
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h9CF4D10A_E5C8F0C7_B034BF23_C9068E30_7D8513B7_734AA78C_C36F947A_2737BBC0
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hACD1447B_AA83C3FC_818BB3B4_A840AD32_14CEB3F3_54CA2E08_9302C3EE_1D695AA6
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h16283205_DB05CD6C_18888AD0_1FE046EA_FD8BF298_DB7D5FE0_FD32A296_89A0C154
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h9C28C210_C01FF7E6_E6D20E04_04E7B51D_020AA369_5DF42597_CACAEA4E_16EF75A4
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h823EE1BF_100B50C3_A2C1BA79_A60BD0D9_47C26D8D_3C3874C6_B8E34A85_925CE73B
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h8F155098_5EB503E8_E4071315_2D132E9E_94DA720A_712D7D6B_7326F310_2BA57AB1
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h2F0C11E4_64E61308_8D6DF2CC_4352AA62_DF6B0719_9EA6C678_2AD9BB2E_78FA04C6
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h8991DE3B_57A9B612_06E6C0A2_AFA6A3C5,
    256'h6D97128C_7811E36A_2829DB02_5EC69547_062345C4_00F5EF1B_06A11965_0A85C302
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h37536DC3_E35040DE_9AC1A6F2_B35C99FB,
    256'h71E1AAAB_3C208383_ADF50311_FF71FD46_921923A8_CD8C6FF9_8F9BDFC2_B205D869
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h0DD35500_E5A51BBA_34A71D81_E9EB876B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h6F1996B2_BE4B58DF_CFB830B9_E25BDAA3
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hE1AFFA91_806D01A8
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h0E4D3302_F22CE229_EA15318B_A7B5D9A3,
    256'hA5BE8CDC_8182E3DC_C4E4767B_D2BF2553_2B7DA107_635E656D_20BCB5D4_30854DE6
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h57A6A15F_AA577395_193CDE4A_6705BD11
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h203330A9_27A8CE1A_C88224A4_41C4192A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hBE1DC426_FEEE2C9B
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hDB154BE6_8E0E3DB7_FC059591_9770234F,
    256'hEA7B6142_B210C1A4_BF574970_3160CC2B_5A7B487D_9B09D7B9_243FEAB2_2AB0D887
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h51C3DA59_67F2CC89
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hF1B0ECA3_388F277F_FAE4319B_4144B76B
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h7C902A9C
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h38066D0B_75EB14BC_511693C9_3E0525CD_DDF6C3D1
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hEC24DF2D_9B070658_CB5B072B_B74E79DE
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hA47A4186_3ADAED04
  };

endpackage : top_earlgrey_rnd_cnst_pkg
