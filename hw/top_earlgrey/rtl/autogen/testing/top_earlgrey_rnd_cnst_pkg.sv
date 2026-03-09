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
    40'h9C_AA47E5CE
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h9200_8344A54D_5DF3076E_61840052_592CE892_21C79084_16255948_D33DD6A7
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h2A71D66B_5953DBC6_03379DA9_EFB2069B_D79815B2_F8D99A40_E7FDC4FB_13143D77
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
    5632'({
      64'hA1832965B9E9EB47,
      32'h0, // unallocated space
      1024'h0,
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
    3008'({
      64'hE7DAA2EA63EA3209,
      96'h0, // unallocated space
      256'h0,
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
      1248'h0
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
    128'h53CE1CF9_E2029207_396945C9_5C9B54BA
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hE6AEF30D_8577834C_CC6CAAA6_3A8E6604
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h338151B9_A23C08F9_EED04CA1_EBB0BDD3
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h05FFB6C4_818054E0_E0EDB0AC_D0B040FC
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h629EA7F8_B17FA88F_EE02E3F0_864223A2
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hE23A8CC3_1E2DE5E5_78D43D2D_CE49E360_CFB594AC_DDF17068_4F6EAD2B_7FEBFE89,
    256'h5523D7BC_4846A485_956C7F90_4B9EDED0_9B89A754_33566F49_63D9DC27_F3ECB11C,
    256'hE3B87AAA_7ABC8592_0B188108_3AFF7BDE_18EACFF8_5679453D_A77D92A1_76B87118,
    256'hAF11CDBE_78D67060_615A20B9_C0740F07_969CCD2D_10A1A6E7_988FA528_AC032E0A
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h6138CB83
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h21BFE532_078BB254_F11778E6_1A83B66E_E9A5E242
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h169AB2DE_3973D027_EE30B8F9_01F644EC
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h7CD3E56C_8ED1EC38_739F1D0D_EB7C7741
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h99CF6DD0_57F44C13
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'h96C1F7F8_D3BF2419_CB13DDB9_AE94F53F,
    256'h3EC27CA3_30488D32_C6E0DAE8_582D6401_A3564A2A_99C85BF2_2458414B_DD59E5F8
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h69568E66_1498FD89_197CCAE8_EA08FF43
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hEFC2BFB1_C6AB5CC6_3E6F4741_E80F777C
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hB7FC0504_1A1B8963_50C9636D_6814D23E_2F5FF127_5EF19959_AAA8B6A0_04D55749,
    256'h84DED1CC_79BD6787_D6663AA5_E622682A_6525E083_CCDDBD2A_1B008057_C22C884E
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hD49D87A5
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h4B862905_F72F7D15_C39AC6E7_FAE58041_147351B6
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h4F1800ED_ECF7B176
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hC6824AF1_D7B6E2B6_FDDE9895_B41FC2D4,
    256'h073AF989_72397E53_10D91A7E_A9A1C3B6_560C852F_8D048544_79CC18BB_2E3F3D20
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h128E70AD_3D98BB12_1D15B823_8AA46970,
    256'hCE17B752_E6FF4919_09506536_19FD7874_B3DECBC9_286CBB68_FF960D0F_00E8E51F
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hDF0A4F7D,
    256'hFF07DB05_DE63910E_4EE4D8A2_C7D4022F_16ED8A24_F80EEBCF_8299839C_103EAE3C
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h60190A71_809B6A5A_28649904_46967288_875D3712_311F9542_5638901B_8B767D3A,
    256'h099A8F41_2D93533C_62835149_4C78333B_654F2A7A_4E47107F_79027B23_395C7735,
    256'h2B307C14_6F070C9E_4D5B1750_7389450D_213E1C24_5F548408_328C1520_6E03110B,
    256'h741A527E_9D55970E_05861E98_4485434B_67345863_48822729_6822369C_8A8E062E,
    256'h0F706992_914A013D_2C133F6D_40755700_26618D81_1D16949F_256C595E_6B66182F
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h02C22995,
    256'h7B7D1597_40CA72CE_50C55920_BA14E126_DCD0A3F6_C9B71D03_E571BEE0_E47E5B49
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h1DDF635E_4E89ADA5,
    256'h2CD5389F_165D0C8D_42FA9EA0_260CA4F6_D5596AF1_A1C00141_E334A3A6_5B682949,
    256'h9D0747EE_9076C258_FE56C2A3_16DD74B3_07B1BCA1_A1A30442_24401EB5_EA95A38E,
    256'h778D177B_54C5C493_B79D883C_F08B95B0_26603D14_66E1C15C_CF530CC0_BC2B4B4C,
    256'h44B7020A_F1BEC6D1_5131C67A_646BB17F_A51F2AE0_8B816677_E65B29DF_EA698584,
    256'h09FBBA5F_06CDD12F_0F425D98_8145AEDE_10B20E5A_E4187D0D_4D4C1378_FE7B8F1B,
    256'h627B9400_77354043_C6B549F4_41EC872A_B56F2FB8_AAD94EA1_3C443099_11FA21EC,
    256'h8F54401A_7D1B9AD3_EDB57831_D70C1C41_5CE48EED_576B7352_22342CB6_A40E912F,
    256'hF845025E_C9EB04B6_3EABAC50_EE569A36_FDE859E5_250DDF19_D6C1C45C_49DC2966,
    256'h3E6B8F21_F803C0E3_655E9F91_CD80A401_7EA02B35_838CDC9B_85BD1900_25F6E486,
    256'h9A896078_0528F451_78668049_99C817C9_A5A01797_47273F0B_3A11D189_7292196A,
    256'hCB0E480A_EA36DB25_93CAACB8_6115E53C_DB92C289_FEBDA009_08DC3E3A_9797DD8D,
    256'h8129178A_8491411A_6EAA266B_344A345B_D55A72BE_48A3937D_B45D6779_4C0B38CF,
    256'h8779F846_8AA73315_928ED7F5_C42DECE8_56F610D1_E4EC3ABD_21C5C0DC_BA126BF5,
    256'hD24D02DA_E5DA1698_66300C46_0BA7FEC3_8953FA4B_12750184_12934065_A1B4324D,
    256'hE709CEAD_C4EA188E_1251ED12_6E573318_2140C4BD_E6DC712A_598352B4_B0822637,
    256'h4E5C5B47_C0B8B964_9E4C3201_638A4541_943FCB10_8D87B58B_2B157C58_6F869E4F,
    256'h3F4E59C8_1690CA6A_0E75666B_0C69B347_2283DC56_C12F1604_26B42A30_FD2E6AA0,
    256'hC2466C11_D0A908F3_5DCAB68A_19B7D903_6908A26F_558B0DA0_8ECB11FC_B2671931,
    256'hDC3452C6_96D2210C_6200D62C_EE223083_BBE2D759_4DC06A42_52A8996E_33991134,
    256'hABF19A7E_A9452274_3C954311_55312362_185EB180_07D21441_5581D324_A057D933,
    256'h208AB530_818C5D1B_27C2B26B_0DCEB860_9C09E8A1_39F30547_69461621_AA9A9906,
    256'h7BDA41C0_7F9A1399_E81F181B_0BE44500_159C02C0_B9E034A5_69C19B16_3D030A98,
    256'hA44CA99E_5E602A38_2A11B124_CFB9B198_B249B085_B6E469AD_B091610B_5911962E,
    256'h6A560246_CA610647_96E8E18B_CE4505D7_2BD0E551_4A15C5E0_4822C0A1_B6EC614E,
    256'h2092FDEA_3F20B743_16520484_D8398AD2_F0F42B48_481570A2_BA846745_A0B1F180,
    256'hEC889517_E7960D16_434C7916_B821E296_85654730_DB0720A8_14CD284A_DF5AB095,
    256'h5D8C7B74_BD9B84A6_AD6E03EE_9239AF67_0C5C1433_1447A819_248EDA19_79C721CE,
    256'h04C21D24_9322EE97_C419D2F8_65C7CCB1_02F29355_12D6FA8A_4CE108BC_03698ABA,
    256'h87A7A14B_F9639D99_B3BD5358_31734E07_A3189988_4F72D3E7_16CA699A_C9BD2508,
    256'h5D56781A_5AA9D902_8B539E71_3598BAED_767E9664_41304188_1A8D9B95_80A88085,
    256'h08758F03_823EC625_EFC2D23A_150897C0_C2B3CE98_C8533E52_D89E78BC_DDD9A4F6
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hADCDFC5C,
    256'h5F76D4A8_E259D88D_FE9B670A_A0DD992B_FE5D2E12_489D2250_4AA7AC1C_67F59CBA,
    256'h5482C1E3_5E6E3335_C20CC778_FC309917_B9C870AB_E0895D76_F862EF81_F419E3C6,
    256'hCDC8662C_71EAC141_666E443C_6492D9BC_F7A82420_750E5DFC_5E3ED4F2_907532E1
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h6413B04D_41226A3A_C89962EF_089605B8,
    256'hA93CCDD5_6CD8631C_FDBDEAA3_13434654_27E6102D_F97CBDE0_73E04A9D_357FBE9E
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hDD57022C_77EDE860_9C409D90_5B3C7819_B26A6743_28819928_C5D79BF1_DB63D11E
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h2136B210_FFE9A7A3_FD76AC0A_13F13263_168D754E_F5FBE7D6_8E8F4509_7966732D,
    256'hD587239B_39F4417F_FEB8E5A1_B7A00BE0_938A1DDB_90F924EB_58E82F5B_92570C74,
    256'h602BB433_043EB070_A5113598_C66D4BAA_1E01C1D4_17C3EFCB_379ABE53_F8AF46F2,
    256'h9618156C_02A6F3AD_CFBD422C_EA0FDCD8_00728C26_8206C87B_6494FAEC_4DF6612A,
    256'h69DA2852_C21FCE48_6FE4ED4F_9F255D3A_F7A92E5E_D7A41B62_59AB6729_6A0E55D9,
    256'h44869EB5_22430DD0_CDAED289_8197C53B_7E7D3856_5C6E3091_7AEE4A78_D1E2509C,
    256'hB683BF47_84FC035F_951AB1E1_71E39980_0851A265_8BDDBC05_4CD3DF85_BA279D88,
    256'hF00749E6_4020B33C_3419545A_777CDE12_68B9C06B_CA143DCC_C43FC7A8_C9BB311C
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hBEF1F0B9_24C470AC_5A998099_85DC415B
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hA1EACED3_82D54C9E
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h378D030E_A5D37665
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h6F2F2513_8426806B_A968F86A_C76091BD,
    256'hE2EB50C3_59174ED2_1D673F23_A9F705DC_E4C2C0E2_7D5B498F_E2BD639A_135C03B5
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h5CE46D90_7D6FA366_5558800F_AFDE8812_4B9E3C2E
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h6D07801B_027BD4E9_BF578B14_6F616B60_82465E44_680CE936_49A84575_B465479F
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h31A97523_4377E00D_28EC32FA_5850E8A7_F607A49B_2CADE12A_F0DD48B9_227A9781
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h79AA2E6A_DC5EA5FD_83777D38_7766BA9E_8C77A65B_1AAD174D_D41ACA70_D3807BA5
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h4E793023_FA711994_CCF5D2F4_2DAFFA84_621AB157_014B7050_9DA8413D_DA43FECD
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hD6C1A586_93232D1C_3E361D85_6AB2D1DC_6455D87F_13C9A467_1446BEA8_56D5FBB5
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h4BB5B253_A70BC372_CFC9BB0A_B38A5EDA_BEE7D224_D1A66837_8437DD24_797B602B
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h068C0A1A_ECA298C9_6A8130AB_336462CE_E1BF8C65_3FDE5A40_A24DF78E_146916DC
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h55F8CE6D_BFAAD089_10FBE182_2C22A17A_376FA131_5C0CB3C2_9CF4D10A_E5C8F0C7
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hB034BF23_C9068E30_7D8513B7_734AA78C_C36F947A_2737BBC0_ACD1447B_AA83C3FC
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h818BB3B4_A840AD32_14CEB3F3_54CA2E08_9302C3EE_1D695AA6_16283205_DB05CD6C
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h18888AD0_1FE046EA_FD8BF298_DB7D5FE0_FD32A296_89A0C154_9C28C210_C01FF7E6
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hE6D20E04_04E7B51D_020AA369_5DF42597,
    256'hCACAEA4E_16EF75A4_823EE1BF_100B50C3_A2C1BA79_A60BD0D9_47C26D8D_3C3874C6
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hB8E34A85_925CE73B_8F155098_5EB503E8,
    256'hE4071315_2D132E9E_94DA720A_712D7D6B_7326F310_2BA57AB1_2F0C11E4_64E61308
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h8D6DF2CC_4352AA62_DF6B0719_9EA6C678
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h2AD9BB2E_78FA04C6_8991DE3B_57A9B612
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h06E6C0A2_AFA6A3C5
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hD85E43B8_C91DA6F4_AB25C7CF_9F2AA0E8,
    256'h7D153BB2_D69984E2_43CFD436_D84266CA_301B5CC8_051FB15C_0DCA6B8F_5E8C495B
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hD35500E5_A51BBA34
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hA71D81E9_EB876B6F_1996B2BE_4B58DFCF
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hB830B9E2
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hD77E228D_8F0E2274_9897B391_954FC06C_255E536B
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hB7279A2B_D0F45178_ADD4099B_463A9BFA
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hDEB0A249_E67A25FE
  };

endpackage : top_earlgrey_rnd_cnst_pkg
