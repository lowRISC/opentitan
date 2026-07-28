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
    40'h25_714513BF
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h54F9_860E448C_5D07DB00_E8054638_A75084D6_25910274_D61E1E16_9C94B04A
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h5920BA14_E126DCD0_A3F6C9B7_1D03E571_BEE0E47E_5B49E80E_3DA39A52_777DBCFD
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
    128'h9E38D4D1_89EC4B43_3E5314F8_8C893A6C
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hB3FD30A8_7C38225A_15108E99_2D14BF12
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h25D4B19B_23F40E35_8F1BF4FE_1D5A50B1
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h0232A8B3_C33A6017_B9703656_1AA26231
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h042404E5_EF74645B_E00EA5B5_67DBB5DA
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hBAC06604_137ECD88_E38E79D9_E08BE982_53A7A2D2_902EA76A_5AB2069F_E29967AA,
    256'h7567085E_49639BC5_6B02698E_D537B28B_E5D47160_4F8672C8_13D59889_625BEE8D,
    256'hA30B81E1_F9D834F4_14FCD66B_581354CB_CB9A3BC5_66D79D9F_58F70432_D8BF8509,
    256'hA79CA1D3_AB83A61A_F330C5CF_D188035E_2F181081_33B38A71_67F82D4B_5453CA02
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h93579000
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hEB714866_B642F492_4E2A0FDC_C2BC723F_2E0DF8C2
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hCD9D71CA_9790686D_8EE0F7C7_49308188
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h1EAE1452_0CC2B374_021DE436_F5703142
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hE83B671A_6BCE2387
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h1F4488A6_C42A38AF_82068B7B_E7F8BA8D,
    256'h1BF0C756_201A1727_75F0F235_9509DD73_1315BF25_DA410FCF_D99656BE_002DA7AE
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h45A09A6E_BDE6CF84_0D02166D_83607964
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h5F80AF64_95172233_0EDD3E68_903F680E
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'hA7217450_DC1F11AA_9BE9BCE0_28ACBB45_FC85DEAE_E9E9571E_205CBA9A_4851B89A,
    256'h0AD9B8E6_0F7B4BCF_8ACBC584_0E79CB08_4D95CA06_12035221_8C90DFAB_74299E78
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h82F53F00_7A8AC1BC
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h70FF9E69_29C3E84F_28BF0FD6_949357B3,
    256'h4D4733B8_A66488DF_290395F5_4AB3E241_69042CB9_86BC5B44_662D0137_60DAEDCB
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hB5FA5622_6EF0EED9
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h56EABF1E_CDA9A207_F17B433D_2A1CB338,
    256'hD25713A6_428E2BE7_E24C126D_319CAF77_543C3201_15098B5B_B025F91F_2DE586B5
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h8554CC04_9223D063_9FA87A17_75AF3236,
    256'h58BFEAFF_9CDFB0C4_1692E067_8F73D76B_5BE50B02_B98C11AD_650A4B19_277A600F
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h1C056939,
    256'h7BFC4197_6AC86B02_BF2B89BE_218ECED8_859F464D_1D910540_EEC6BA04_86F07CFF
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h2F622D58_458C443F_3D8F8420_06873966_82942C71_86384099_5E006188_414E9860,
    256'h471A3B0E_4F69537A_0A5F426E_6837295C_9F6D8304_46287D89_4A264D16_1C5D2243,
    256'h341D8167_78311202_65960B50_0F930C15_904C237E_753C1E8E_6F1F2110_548A2E03,
    256'h0836306B_6A142577_9E320119_3E5A7672_1107557F_59492463_529C5B85_33647073,
    256'h4B9B5617_351B5780_74482A95_91180D3A_516C0597_9D2B9A09_7C79278D_13928B7B
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h42C85E45,
    256'h6F3B26D1_5F5584BB_9879BD24_97852C23_D0FA289C_3348CE36_4ED53497_0E1FD45E
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h1F106442_231F91B9,
    256'h212B3622_C9F50C0E_DCB89C0E_28E03AB4_E41CC3A3_D292B181_E0858D61_CF69EEE1,
    256'h1B9B70BE_DB50E1D1_86997F44_A2370A6A_0C768290_000E8008_CA1BC154_F833B4D4,
    256'h6C2C1074_46DB35E3_27063B62_28965D74_D2514359_FAA5E09A_A472BA5E_56C5D6D4,
    256'h054BA0D4_A4787417_9A08C597_70F05A34_02312C52_6E905F88_856B5B1D_CAA2BB08,
    256'h1CE07CEC_3CA4A5D1_DD3B8E59_5DEEBF04_095AD9A7_5AC600E7_23A24B81_1F788DA7,
    256'h36016F23_D9CEF7C4_29F02930_65518A2C_567210F8_72166905_51930D21_526A86F3,
    256'h970B3651_8921A6B0_F632506A_B4652351_401879B8_A3C84B92_44AE6367_AA1AB524,
    256'h38CEB385_6FE1C0C3_13570A73_1A9FCA64_9703279B_BAF5AD92_47D67883_295441A8,
    256'h2E2AA756_68971E82_22E6F599_AD70B300_5890A454_50950326_480D87C7_710D7E77,
    256'h9600C69A_11EB1B59_6A980A85_3E149BDF_F8121017_84620955_78428880_F7A2250B,
    256'hB10204A7_C509475D_88F4871E_66535092_5A931AA8_D53CB3DE_B031B402_69376CFF,
    256'h4705431A_781D3160_76ACB98D_3C46CA8B_97A9A687_BC6942C5_B69149A1_14C28F2B,
    256'h25310434_30CAF079_3F15F01E_8C5D5D33_E50E359C_20F92D83_D4871449_58540B96,
    256'hB4304605_6AC249E7_45493326_60905D86_7F0DE84D_14C7C91C_555632DF_21D43499,
    256'hF075E037_57A05149_CFB15A57_BDD2111C_C06E859C_AEB4BD8C_1DADCB01_C4372023,
    256'hD6818AE3_F28684BC_908AD435_03DEDB27_1345A17A_613A8AA1_920566B7_8B43E025,
    256'h5CAC10A5_981FD51B_6838A9AE_D62DF6B7_CCE5922F_2DACB9D8_EF01157C_05D92FE7,
    256'h962169A9_E26C7719_A0DAEA00_0B9F9BEB_9EF93F4C_8BBEEA21_C8B62A11_9B5D54F7,
    256'h0E8E5CA2_F71BB45B_224E716B_DD83CC65_C21A97E8_BB3AA55A_DAC3BEDE_C608E333,
    256'h19B9C2E8_77E4F2E9_C138573C_72896125_22F1832A_53933D58_4AA63488_B86717D1,
    256'hC8B77963_A6E96F4C_94D3547B_92C1C0A8_A46C5970_4DC33E89_23AC68BF_4B0524E0,
    256'h2BC90C15_0501A77C_246C3644_23459347_5F51724D_064ADA38_4EA928D8_C2255716,
    256'h8061811A_EF0231C0_C1302166_0EAB9719_EABF262D_28016E29_CF0919F0_64265198,
    256'h5169848A_E0B571AB_73117C8B_4D41A528_4D88AB32_FA256428_4ACE97EA_58A5E4BA,
    256'h52C6C0E9_71D4B63E_4E6594E4_E2B07DC5_8A28A012_D548C45B_15E64479_DA5B5FB6,
    256'h89BF0D98_E8ECAC0F_E68AE862_7D0DB0F2_F67C61B4_DE9B42CE_627D17BB_84C40E61,
    256'h616D5220_30389E7A_1AE2B12C_737C9D54_C270B501_3B531402_97468BE6_CC5A96C9,
    256'h4104CD30_1F9C5DE6_B40D72C8_C9098AB5_9E40AFAA_F8293B7A_55075853_C189669D,
    256'h65A8E9E6_757BA451_15DD2486_0A2A5653_0AC4F6AE_2241D598_1C717A1B_DAA9137F,
    256'hA96374F1_82E065FD_4A686088_DD120523_8226A257_4677CEDD_26C03726_3E0E6E39,
    256'h6163481B_9988FE9B_0D242411_68C5F3EE_FFA80807_501A6442_3B22F483_13FBE318
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h823EE1BF,
    256'h100B50C3_A2C1BA79_A60BD0D9_47C26D8D_3C3874C6_B8E34A85_925CE73B_8F155098,
    256'h5EB503E8_E4071315_2D132E9E_94DA720A_712D7D6B_7326F310_2BA57AB1_2F0C11E4,
    256'h64E61308_8D6DF2CC_4352AA62_DF6B0719_9EA6C678_2AD9BB2E_78FA04C6_8991DE3B
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h7DC0BD0C_9152FDD9_2FCF63D6_B8738B51,
    256'h3D593778_3A61084C_8A61BE9C_8ED1C970_2C29AD1E_8FC95BC7_8A6BA30E_4112DA95
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hDFC2B205,
    256'hD8690DD3_5500E5A5_1BBA34A7_1D81E9EB_876B6F19_96B2BE4B_58DFCFB8_30B9E25B
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h7E890659_0E38B645_66029F8D_E0CD049E_E4D6FC61_A44D007F_10FF9354_CC0FC532,
    256'h52EF3D8E_5B6492C7_2E724C23_F9588712_E94E94B2_885A65CF_1FDCC0D8_EED703DE,
    256'h17765C42_F46B358C_53183F70_47E5449C_D3280A9D_F3F60D2F_2DE281BC_6F08F216,
    256'h3E0CA08F_F7E84F60_A598487C_6CAC2936_E7CEB371_1BC93BE3_E6833956_62D47B07,
    256'h145EDD6A_79BA8637_A7B9AB90_2221348B_1C2C261D_2AFE4124_821AC630_33C11105,
    256'h67BE3C19_C873AA5F_A1B5DB40_D5FBD28A_96CBA999_20A6555D_6EB1BFC4_C2FDEAEC,
    256'hBDED75F1_1568D9EB_95257A49_A2B0D13A_46F509AD_7851D02B_9A27B757_31AE7DBB,
    256'hB869CA13_1E634B77_97F84A0B_85B47443_F0C38450_DF9BA801_6D8091FA_AFE1A3DA
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h1496_8D889D37_04986EB0_BC1882D4_8AA39CCC_A5C2D1C0,
    256'h05143F9E_0FA6E5AC_FD6E5F02_362567BA_5CD45472_592CDC53_019D7E95_66780B51,
    256'hA7CAA256_0370905E_80CF21B1_8AFD2869_325CA009_09F9EB5D_304F63A6_90FC9806,
    256'h3BA255D8_C40BBCC5_D3511F86_EF2DE570_750CFE9C_A0624213_AB76E43E_1EAD978E,
    256'hFB6371F2_3297A957_74E2B16D_0964A6A6_87106415_C690AAB6_921D61C5_31620ED3,
    256'hA135A442_97E8C538_0791D314_13EADBC6_2092B39B_C6F7C2AA_B058418B_C6A9F3C8,
    256'h43CD0A19_11504D11_C765D9E8_2E07B211_8CA8CA4D_3242872E_55247268_AEE60D8D,
    256'hB7EBC285_3A01AF0F_828211C4_C88A86B0_C366D69A_83094BEE_E89044AD_1B274122,
    256'hA16156B0_A59CCFA9_2310340E_58A3CC89_E2F21D30_948B5721_451A9B3A_301221D1,
    256'h8F4EA09D_824A9F17_8D0BB049_9604217B_578E58A4_9AC9DA18_BA804EA6_C575F288,
    256'hF2BD2CB0_1F8D086A_2DAA3A9D_C7A8B848_FCD226DB_364B48AC_17739198_ED998041,
    256'h86AB44E0_CE3C31D5_42CAB65D_AE4E4A5C_2FE12230_C1B6DC66_569C4A16_50595137,
    256'h2A67DA70_4110F39C_2F7F2914_D46E1818_95B58096_5E25C4B3_B919FF15_63D41EE0,
    256'h5B7A9028_8813A0DF_102A0244_6A15A927_488E335A_5D857D05_38286F67_413EC626
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hE4CEA841_22890180_EA765E57_BE4FB2CA
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h7A5674F5_969C8D4E
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h0C3C8955_221493BD
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h66587525_DED54B8E_9E80FDAC_5BE303F6,
    256'h6A0008E4_CAC73C27_8EEB4B19_F05A150B_DC5EBE7C_FD8C8889_1377907A_44D1BA94
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h8D490158_037A6872_A3A6C2D9_9FE9D29F_1AADFAE1
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hE290469A_68314D76_067A213F_0A66A9C9_170EAE32_6AE272B2_AE733612_4EC0584F
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h578BE735_54751936_E4D1FF12_DFF48308_4C35115C_52B69C63_F74A87B0_347CE357
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h9B2EF788_B20605BD_4CE678B2_D537F08E_7E3E95ED_D580D731_E1C74067_A186866C
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hA7421209_62203D0E_0FCEE99A_A016E58C_2EF6A6D3_1B5F29FE_DB4AD5BA_49EDACE7
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h1FAA96B0_563AC8AF_C3B29DED_0FC2497C_EB6915AB_2DEB1F0F_78A85399_55EAD3A8
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h43EC2520_E73AD7B0_5850D497_81309822_B4B62245_860418E3_183D26A9_3EF65692
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hCA9BD250_43DB7F2A_30DCF83E_154244E2_61591BE2_ED271407_428E429A_C3600F51
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h4434966A_473B3CD9_4280D27A_0E89F371,
    256'hB3FDE779_DEAFC928_3C07F0D5_38309767_DE8E449E_E3CFAAB0_E9E8305C_5BADB463
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h3EDD8196_C3ABFE0E_7568564A_BD46FE8E,
    256'h5EF12673_21A80B76_CADC596A_D13459ED_F5132788_E2DDD919_1E7497D9_F99C47D2
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h23C66873_EBDEE1C5_1E5F79F4_A352D5FA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hC995CC06_57B1159F_10E61CE7_AF32C3C2
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h7F638C31_642270FC
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h44C67C53_A06D9FBF_780A0B2F_962748F9,
    256'h7A32DD6C_23CC940A_A83D8FE5_31FF7CE7_06985371_AF5A5E68_04AE1159_21D182DB
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h75BC7ACA_00D36BC6_B335AFA9_CEED9F39
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h9B00525A_94ACA953_CDBA0D9A_5BD3C88A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'h31CCC04F_C3F1F6F0
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hEEB4C504_FBE66DF1_F773EBA8_E95B611A,
    256'h7E54898F_D62BCE35_4425F30C_ED2C10DD_A4A63030_420AB2F4_968848C7_5E64BC65
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h370CB564_E67FA1EA
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h7B1F1BB9_5F4042F5_A47FE72B_0298966D
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h3AAB980E
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h63568C0B_7FB24B9E_38F426A0_30C7A6F0_152BCDF5
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h78462F65_12ECDC87_07EA555F_702EC608
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hB8370AC8_ECC1FFE8
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'hE11EB85E_B1442A75_F7F69A30_931A5056
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'hB64EDD69_D644BD96_4127B767_62744CCD
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h52C2607A_A7FC45AA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h8653836A_39920B0F_29B8D62A_EB6708B4,
    256'h67F707E2_C5EE88B8_3DEC9103_D75BD07F_CA92B431_BC9E734D_95605B55_1732C127
  };

endpackage : top_earlgrey_rnd_cnst_pkg
