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
    40'hCB_024D6F8C
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h7556_643106D8_5E250F9A_09C14880_967C694A_2CD68E85_14DE1E32_45100703
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hE6AEF30D_8577834C_CC6CAAA6_3A8E6604_338151B9_A23C08F9_EED04CA1_EBB0BDD3
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
    128'h05FFB6C4_818054E0_E0EDB0AC_D0B040FC
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h629EA7F8_B17FA88F_EE02E3F0_864223A2
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hE23A8CC3_1E2DE5E5_78D43D2D_CE49E360
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hCFB594AC_DDF17068_4F6EAD2B_7FEBFE89
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h5523D7BC_4846A485_956C7F90_4B9EDED0
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h9B89A754_33566F49_63D9DC27_F3ECB11C_E3B87AAA_7ABC8592_0B188108_3AFF7BDE,
    256'h18EACFF8_5679453D_A77D92A1_76B87118_AF11CDBE_78D67060_615A20B9_C0740F07,
    256'h969CCD2D_10A1A6E7_988FA528_AC032E0A_6138CB83_16FF95C6_5CD7A1A7_68B06E01,
    256'h06D60EDA_0F1BC67A_DF85BD9A_56EA088D_33FFAA6A_1155AFB0_169AB2DE_3973D027
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hEE30B8F9
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hFE596A98_4952F12A_10B0DF6F_C08E6E3C_5BA7A3C0
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hE6596E87_F9F973DB_98AAA293_568FD1F3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h1A016593_9D819D15_18690E64_73CDB247
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h93916350_57CA1045
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h3C430AB7_72748764_115009E0_39CC9BAF,
    256'hB2F9597D_48F9E77D_F31CEF66_3A3056C4_8D0E5E85_6BF4E209_8AA90661_877E4E2E
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h3E2F5FF1_275EF199_59AAA8B6_A004D557
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h4984DED1_CC79BD67_87D6663A_A5E62268
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h2A6525E0_83CCDDBD_2A1B0080_57C22C88_4ED49D87_A5B56BA7_353C5321_42F50667,
    256'hE220C5B7_24C3FDB6_D060653B_42A96F88_B574E4D3_814F5116_B3E6F3E3_31DA1182
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    64'hDBC29C89_4F1800ED
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    128'hAAD24A56_86F978DE_2F7189A4_044FF102,
    256'h5A70DCE5_F54C2EBC_89A7F287_6AD95832_148D0485_4479CC18_BFAE3F3D_2076CF7B
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h7D513AEA_01E9EE42
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hB62A538F_363D42FA_FB9F820B_D8512591,
    256'h1E667DD3_3F83067C_5DC6C254_1A0D86A3_9E1D2EB1_FAEB3424_AD771B20_1A3D4583
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h7FE7ABF6_D1D47559_61FFC8EC_34870E2B,
    256'h4A8C450B_C24B8EB2_C1B59769_91B3A4F1_27BA683B_26214B03_5C68DB94_C3918DC1
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h5C0CAE7E,
    256'hD7FE6C45_D1534FD3_90C7B068_CFE89687_94DE88E8_FF4ADC3D_02EBFA0A_1D5FAA5E
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h3A4B9583_6675195F_84465A2D_54244D26_9A8A727E_6D023C67_2F59118F_8D974851,
    256'h6A1D824C_63583D61_773E077A_6E50884E_7B711433_3F324498_761F1E25_5C800079,
    256'h3B2C4F37_94299B86_13089E36_70435E93_575B6962_15092238_1264019C_0A1C9D04,
    256'h90600353_999F0B6F_7892681B_7C6C5521_0F31205D_7445054A_47739652_6B2B5685,
    256'h7F28890E_18308C41_2E8E0D27_8B1A427D_39491635_1065812A_40870623_1791340C
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h23F40E35,
    256'h8F1BF4FE_1D5A50B1_0232A8B3_C33A6017_B9703656_1AA26231_042404E5_EF74645B
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h98252C01_F83B9DF1,
    256'hDD1048EE_A73D9675_AA193246_801790B1_F2B4D5B9_F2E08A18_D909C99C_DBF3348F,
    256'h8B6F127D_556684BA_A9CE17D8_C5BDED88_45545C01_7D27DB65_07BF9832_86D622D2,
    256'h76B89D76_6A2BDA91_89EC229E_B614B083_0DE474D7_B0147B35_42544580_402577B9,
    256'hFA775FE8_716B0517_5A7D056D_D45408D2_6E18665E_C9ADF06A_52DC2621_276DF968,
    256'hC20435DC_9A920804_74B56B1B_FF079206_F35E10C2_F103F978_AA215AA5_821127B7,
    256'h801B9928_028EF0BD_F1945093_2166D374_64B8E745_B0C00A43_C19ADA3E_AA4C5007,
    256'h39D92532_EC1AEDFB_96753426_C548D47A_1DA37AB8_5FEB3519_5722430A_12365A0F,
    256'h22530201_9091B9CA_05ECEA57_13959407_841C43E8_6C46507F_D353D23E_5E9B6718,
    256'h0E6A17D8_E50C38A0_8650B630_5BC98EF3_9E1C11C9_C07B0CAA_D49A7DD3_C53E1819,
    256'hD431C45C_B8531A4A_5B7D91D4_7C7E3C40_38E9A959_EAD994D8_00ADB1A0_043C0091,
    256'h302F732F_83A20518_988999B3_87CB483C_AE8094D2_59159EA8_D2E14B5C_97136EB0,
    256'h0A2A0A98_E6242530_F8EA78D3_D9157396_9C2975B4_046BCB48_99C75129_26DE6116,
    256'h5AFAE248_A3D37DD2_9CAF5510_0B38CF82_308DBE4A_A7ACE99F_CED1F5E2_2DEF2A39,
    256'h49C6AEF1_0D1E4EF1_80EA4F8D_D85371BD_498137C5_5A4D02DB_75FB1695_D70F0C7A,
    256'h40C460BA_5C15E106_E79053FA_D2C7AFC1_8412A740_5D81B5DE_0C937A42_4EB40C2B,
    256'h0D748FE9_951EBA26_E559DE0C_BF450311_B5A4E229_73054A96_60D4AD2C_268A0F12,
    256'h8C64B5B4_7C0B8B96_B4D925E1_AA3D8E83_9509471B_69CFF2C4_2361EFA2_CAE95F16,
    256'h1C3DC485_CFD3963C_05A6129A_A584599B_5243A8D1_C910F76F_856B1031_60426BD3,
    256'h030FD2E6_AA25246B_211D0A97_CF35DE13_68A34881_90369087_2204B2D6_2645F03B,
    256'h2E8866ED_8926B8C1_FD750D14_B20AB448_43188035_8B3A09FC_8D6D8ABE_FCAAEBD0,
    256'h7AC5279C_D6962A33_2C12913A_1E31F88C_AB468F53_EEC620D5_6074C928_15F64CC8,
    256'h22AC09C0_631746CC_54ACC5C3_73AE3327_027AB04E_8B9F3A24_151DA718_588689AC,
    256'hCB21067B_DA41C07F_A2139A6C_1F181B0B_EC450015_91AAE4BB_A034A569_509B163D,
    256'h030A98A4_4CA9A6A4_77980A8E_0A846C49_928CFC29_2D8B267B_985B6E46_99667E0E,
    256'h05842D64_9611962E_8A560246_CABB0647_96E8E18B_CE4505D7_2BD0E551_4A15C5E0,
    256'h4822C261_B6EC614E_2092FDEA_3F20B9E5_D08C9481_21360E62_B4BC3D0A_D212055C,
    256'h28B0E119_D1A71A0C_70F90EC8_89517E79_60D16434_9A516C12_1E296856_54730D87,
    256'h520A814C_D284ADF5_B3C955D8_C7C04BD9_B84A6AD6_EAE40FC3_48E6BD9C_31408B34,
    256'h331447A8_19248EDA_1979C721_CE04C21D_249322EE_971519D2_F8653D8C_B1031693,
    256'h5512D71E_8A4CE108_BC03698A_BA87A7A1_4041639D_99B3BD53_5805334E_07A31899,
    256'h884F72D3_E716CA69_9AC9BD25_085D5678_1A5AA9D9_028B539E_713598BA_ED767E96
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h3335C20C,
    256'hC778FC30_9917B9C8_70ABE089_5D76F862_EF81F419_E3C6CDC8_662C71EA_C141666E,
    256'h443C6492_D9BCF7A8_2420750E_5DFC5E3E_D4F29075_32E179EB_EC7ED7D3_A5EF4982,
    256'hF73ED91C_4B1CD0C8_5EC5E548_B40184A6_9EB1E543_96460E36_C55C459E_FE9E4383
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hB3B8145B_84219701_BD602251_D1A7280C,
    256'hF1F7C7F2_13D9D985_AB28C0A5_7B8B3739_27112D4A_06D562F0_EFABBDF3_19E5EE9B
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hCA6BC0B9,
    256'h6812DE7C_775A54FF_19343CB3_2040B349_0768889D_27E0BA85_88D34C05_BCF127DA
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hCBA9D4DA_F76D68E2_C5126323_1D79F8BC_88D05773_C25A27F4_2D72AD61_75D10682,
    256'h13BD4510_2120461C_0993B0EC_FF4E140A_F253FE98_B9EF87B8_A6399632_6C174D3C,
    256'h642CEA74_3126C776_A5DF9AAE_B4BB36A1_8E9041D3_34DB16F3_9F7FAA3F_8DA7C93D,
    256'h7092D77B_196BF6C0_66D2ABE4_4233E68C_EEC13E18_00C41135_5B15EDE7_DD4BE91E,
    256'h022F240F_9B2B8F77_6037D92A_04B2B585_58A0014C_E00CD50B_DC5469A3_2852BA8A,
    256'h1FA4486F_407C4FBE_255D3AF5_C82E945E_05C3AC1B_6259AFCA_67296A0E_55A8FD44,
    256'h869ED822_430DF9FC_E3FB8981_97B7E8EB_3B7E7DCD_38CE565C_6E3091C6_7A9D4A78,
    256'hFAF149E1_509CB683_BF4784F0_DE035F95_1ACFCCB1_0771B399_800851A2_D6658BE5
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h02030621_A4D3D738_71FDAF5A_D0C1DD1E
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h95F99D71_29CA6861
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hA4425B9C_C42EDBA8
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h6B879784_62C36608_C73D622A_B25D09CF,
    256'h507FDA8C_50540F7B_3BA73947_EACA7C2C_92353DE9_6C475832_FC249AE9_FC52D162
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h85E8B7F6_3BF28A31_0247D131_C9E59677_EA9305A8
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h227A9781_79AA2E6A_DC5EA5FD_83777D38_7766BA9E_8C77A65B_1AAD174D_D41ACA70
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hD3807BA5_4E793023_FA711994_CCF5D2F4_2DAFFA84_621AB157_014B7050_9DA8413D
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hDA43FECD_D6C1A586_93232D1C_3E361D85_6AB2D1DC_6455D87F_13C9A467_1446BEA8
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h56D5FBB5_4BB5B253_A70BC372_CFC9BB0A_B38A5EDA_BEE7D224_D1A66837_8437DD24
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h797B602B_068C0A1A_ECA298C9_6A8130AB_336462CE_E1BF8C65_3FDE5A40_A24DF78E
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h146916DC_55F8CE6D_BFAAD089_10FBE182_2C22A17A_376FA131_5C0CB3C2_9CF4D10A
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hE5C8F0C7_B034BF23_C9068E30_7D8513B7_734AA78C_C36F947A_2737BBC0_ACD1447B
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hAA83C3FC_818BB3B4_A840AD32_14CEB3F3_54CA2E08_9302C3EE_1D695AA6_16283205
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hDB05CD6C_18888AD0_1FE046EA_FD8BF298_DB7D5FE0_FD32A296_89A0C154_9C28C210
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hC01FF7E6_E6D20E04_04E7B51D_020AA369_5DF42597_CACAEA4E_16EF75A4_823EE1BF
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h100B50C3_A2C1BA79_A60BD0D9_47C26D8D_3C3874C6_B8E34A85_925CE73B_8F155098
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h5EB503E8_E4071315_2D132E9E_94DA720A,
    256'h712D7D6B_7326F310_2BA57AB1_2F0C11E4_64E61308_8D6DF2CC_4352AA62_DF6B0719
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h9EA6C678_2AD9BB2E_78FA04C6_8991DE3B,
    256'h57A9B612_06E6C0A2_AFA6A3C5_6D97128C_7811E36A_2829DB02_5EC69547_062345C4
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h00F5EF1B_06A11965_0A85C302_37536DC3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hE35040DE_9AC1A6F2_B35C99FB_71E1AAAB
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h3C208383_ADF50311
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hC4564278_F7EF9E82_75134F5D_3BA60A4E,
    256'h5B79422B_94F0BF97_3164ABDB_88601F23_7BA40543_681B309B_76E3CEA2_0691173F
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hAE3157B7_279A2BD0
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hF45178AD_D4099B46_3A9BFADE_B0A249E6
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h7A25FEEA
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h1BFB401D_1FF454C2_CCCBAE6F_A4C2CEC0_9BB20792
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h57A6A15F_AA577395_193CDE4A_6705BD11
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h203330A9_27A8CE1A
  };

endpackage : top_earlgrey_rnd_cnst_pkg
