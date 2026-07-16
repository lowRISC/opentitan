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
    40'h23_06AF306A
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h65F7_16926042_26219468_F6E56134_0455D84B_3118038C_89DE28E0_125C5347
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h071BECA6_F194EF96_F3E535B5_8F2ADAD8_2B175FE9_EA1C326A_6610C111_7744DE61
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
    128'hCCBFABD3_E1FDA667_E0408247_8C14DB07
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h0A6129BB_2945B88D_C6CFCF2A_E02F4701
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h0CB666A5_E22D3320_F89CAA47_E5CED5D2
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h9CC9CDB4_68773EBA_CEC14DA3_4C505AED
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hC70EA184_C7A34193_D59C735B_5B4E2CBE
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hE5AB93CB_024D6F8C_0C700110_CBF01425_DAF5141D_F19A882A_71D66B59_53DBC603,
    256'h379DA9EF_B2069BD7_9815B2F8_D99A40E7_FDC4FB13_143D7753_CE1CF9E2_02920739,
    256'h6945C95C_9B54BAE6_AEF30D85_77834CCC_6CAAA63A_8E660433_8151B9A2_3C08F9EE,
    256'hD04CA1EB_B0BDD305_FFB6C481_8054E0E0_EDB0ACD0_B040FC62_9EA7F8B1_7FA88FEE
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h02E3F086
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h007365C2_7A977F51_28DE6B98_9BEDE51E_227E5088
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h6C7F904B_9EDED09B_89A75433_566F4963
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hD9DC27F3_ECB11CE3_B87AAA7A_BC85920B
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h1881083A_FF7BDE18
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'h8B26A7FE_3397149E_76D1BED3_E2D87D36,
    256'hA520C520_90647326_DC02B02E_5043D485_AC63EF2F_12B19CB9_DA247E93_D1795CFA
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h1155AFB0_169AB2DE_3973D027_EE30B8F9
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h01F644EC_7CD3E56C_8ED1EC38_739F1D0D
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hEB7C7741_99CF6DD0_57F44C13_E25C7A58_77BC5242_E6EE63EC_DF458AE6_596E87F9,
    256'hF973DB98_AAA29356_8FD1F31A_0165939D_819D1518_690E6473_CDB24793_91635057
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hCA1045B9
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hBA3A75FA_D83154E2_433AD89A_988595A0_27F1BE5C
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h7CCAE8EA_08FF43EF
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h4F43A64A_9676A3E7_24233E42_3441DE84,
    256'hC975F4A9_C0EE0C95_5A327A2F_815ADEB5_188AE1BF_06D7DD0D_045B3FC5_EAC6CBF0
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hA3A2BB55_C49FBC29_0B797876_D271BD8C,
    256'h7AEC5800_F3465BBC_984305E5_381D89BA_B73B5632_C09FB1E1_90502143_CDFDAB69
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hF565C1B8,
    256'h7D687EE8_37FC119F_5BBE7395_CAC38919_C27006C2_3E142591_0840042A_75ECC25D
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h77065639_9C686F11_46168449_19716213_21437283_26340A4A_9429329E_2A92752E,
    256'h7B1A606D_903B4B4F_8D956104_0F5A8E10_8C1D158F_09186523_204D5F8B_782D5450,
    256'h9F7E2C7A_35330C53_871F804C_41816A45_0B177698_936C8863_02038627_823C8970,
    256'h57917364_3174405D_2B14127F_0744471C_5C3D998A_300E5E58_7C3E2F38_9D693666,
    256'h08550537_8597791E_48965925_24281B9B_6B3F525B_0D42019A_517D3A00_6E67224E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h402A8165,
    256'h10C535A8_164939D9_7DF7421A_D4D2C18B_270D422E_C39C41F7_27D130ED_9B18B90E
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h6965D89A_FD0F9BCC,
    256'h3EE0B096_F1881E82_B0EBEA37_26A7E96D_DA730EE3_0E83018C_83294F81_01C6A122,
    256'h7B0E861D_B31ECF44_50A00B2B_53014689_19636135_305672B2_2A858963_8965278C,
    256'hD440DD51_68D1AEE3_786AF1A2_5C11184B_26386DF0_45564770_89C0DDE0_C4C77B92,
    256'h90652216_D0098C2A_7B75F264_91547E67_3E807C6C_DB76CA38_01AE7DEB_95E09F39,
    256'hEFEA4B14_43EB63C5_D20BE2CC_456873E7_2AA805A9_16C6144C_B29E393A_771F803C,
    256'h722288C2_9005B864_1A73D617_0090C8D0_784FEEC0_10FEBB5F_9AC472AA_D02378EB,
    256'hA50D73C2_B35F2D62_9C5F22E1_5AC9C647_5812613A_949209CE_1956E5F6_FEBE8BA4,
    256'h334025C7_9DE512C4_8E66D95D_EE74C5CB_CAB80823_51B9E961_93D72A68_12C145E5,
    256'hF19A86F4_8C719F14_B6D96B2B_A13A8EB7_57463838_93965345_317B5D64_593D7A7D,
    256'h1E441C17_5C0B67F0_D4414FB3_AA2D4020_20A17146_94090952_92E93424_1141A822,
    256'h65EB84A7_4B995AC5_AACC6A53_44AFC38C_F86F9BD2_A993B9F1_D3B5C163_0B7A99AA,
    256'hB31F8478_3A66700B_D8DCBC52_67A02DA4_68E16957_03118C29_D4A6E6C6_D6B0C2D0,
    256'h47BF1860_C6D0C937_C4210A16_E59E6010_55479C49_B8CCCC68_EF331166_86A584A8,
    256'h352B4B08_FD9A9987_C760B984_5A9B2C1D_29150820_FF2C423A_B4B2B1D6_1995737D,
    256'h8FD39597_05A20BEE_51A22055_F51CA29F_E77E7A8D_826AA27B_0FD2E1B0_91920474,
    256'h2A1F3CD7_77107622_8DA421FA_C1962B42_CD3B29C7_02A11762_8688D14B_286210C6,
    256'h201FB2CE_3E9D5FDB_15DC536D_5C2094A0_241AE8E6_445FF788_6696A7D1_489D0F23,
    256'h1758554C_48DC1689_55B17214_412AC0EA_EC5063AD_B32464B7_A49739CD_49D499FE,
    256'hA570EDF0_C57F0BAC_04F18DA8_1C9242F9_0C01B9C1_F3B4EC1C_32C3B44F_25CA6B09,
    256'hD1757A60_43574BBA_1C9848C9_8E9910E1_8990D635_4833DCD2_1C307911_399581F1,
    256'h81B0AB84_500159B5_2A9B5E03_4A569B65_B163EF80_A98A44CA_9955E602_8A846C49,
    256'h33EBDBAE_25A685B6_E469B86D_C1631FBD_51962E46_560246CB_15064796_E8E18BCE,
    256'h4505D72B_D0E5514A_15C5E048_22AF21BB_FC614E20_92FDEA3F_20B742F4_520484D8,
    256'h39C652F0_F42B4848_1570A211_9D16829F_BA83B222_545F9E58_34590D2E_F45A1E29,
    256'h5951CC36_B68824CD_284ADF5A_10955D8C_7AD0BD9B_84A6AD6E_03EBF239_AF670C5B,
    256'h60331447_A819248E_DA1979C7_21CE04C2_1D249322_EE97C099_D2F865BC_0CB102C8,
    256'h935512D6_CE8A4CE1_08BC0371_2A1E9E85_2D258E76_66CEF54D_60BA4D38_1E8C6266,
    256'h213EF74F_B09699AC_9BD25085_D56781A5_AA9D9028_B539E713_59867E96_64413041,
    256'h881A8D96_02A20214_21D63C0E_08FC0C97_2D23A150_897C0C2B_3CE98C85_33E52D89,
    256'hE7877669_3D96D1D2_8FBA1645_0DCB40C5_67B4A602_DD96B5BB_21A81B8A_C64EDA4C,
    256'h047F92B0_D2E81813_9C5830B8_931C8A62_0F19E3D3_7C7D4062_B9429557_D822850B
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hF0C5DE01,
    256'h9FC073C4_C599518B_F1924441_728893C6_52D73724_32FCC4D3_092BD638_3FDBA352,
    256'h79FCBCD2_BD2C1319_E71A293A_C3249AFC_143E8770_E304FEE2_D365DA6C_4A29010A,
    256'h99EAED07_3BCBD6E3_EAFA23F4_8EEE34D3_1387B45B_91CE49E4_E6B58794_1D1EEC35
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h0E63C8A4_D623AA07_34B5277B_242DB3E9,
    256'h9F313384_6457F3B5_5E89C7FB_00327F91_A112C165_2C1F5B2A_F5AE4DED_D052B89A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h3335C20C,
    256'hC778FC30_9917B9C8_70ABE089_5D76F862_EF81F419_E3C6CDC8_662C71EA_C141666E
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hA37FDE3A_1A0C8671_2D7BB5CF_BE7029BD_00C49915_EB94260F_F37665E8_BB527A47,
    256'h97C68E1B_101F8D53_0988D18A_DF0BCE17_F8E50839_3B69D86E_164F3062_D24DAF0A,
    256'h35C92ABF_229BAAB7_21067455_50FF73EC_6C1D93E4_95BA2EB3_18DBFC61_2587E9F9,
    256'hEE4EA141_B023428C_AD2F4A0D_E7665803_D5598085_049851A2_C1CD726D_13B6DDA9,
    256'h4C278F07_B8A4F6A0_34CB545A_A77C1268_6B143D3F_31E01E63_9A8128CA_676A19C7,
    256'hFE5BEFAC_409C6077_B2C257AB_9DE302C3_5FB92C37_89919F11_E6C02B05_DA568B7D,
    256'h38EDAEFA_EA33FD78_6F83F0CC_D6455CDC_36F44696_43B19EA6_8401B448_C5F2C8D0,
    256'hE24B1CFB_F18249A5_D3D77E79_E132F590_D43E5E5D_0E752024_A8F7BCD9_92643C44
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hEB8D7785_A7BBDCE1_D6A02B6F_0F24F5DB
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h8EF02F9F_B0A4023D
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h8F96A41F_062BB66B
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h48A50E8B_705CE538_D7B20FEA_245D1BC9,
    256'h69B11839_EBB6E429_6842D160_F77CC369_1EF47EF3_355968F9_9E02BF57_CCE80848
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h03FE383A_5B8AD099_E0EC2345_6F2AE5CD_434373BA
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h378D030E_A5D37665_D43A035F_4EA1E463_032A3A8E_24B4547F_8B0DB0C7_7E902776
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hB104C3A9_DA020306_21A4D3D7_3871FDAF_5AD0C1DD_1E95F99D_7129CA68_61A4425B
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h9CC42EDB_A88A15B7_52539FB8_E598F891_C2BD3162_77126EA6_934D3749_740A7CE7
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hC92A49F7_1747D5A7_E3B7E444_732A39A6_9F03F5A8_8525A587_CEDEA909_13BBCE81
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h4E6794DF_2BDD99E6_6D07801B_027BD4E9_BF578B14_6F616B60_82465E44_680CE936
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h49A84575_B465479F_31A97523_4377E00D_28EC32FA_5850E8A7_F607A49B_2CADE12A
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hF0DD48B9_227A9781_79AA2E6A_DC5EA5FD_83777D38_7766BA9E_8C77A65B_1AAD174D
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hD41ACA70_D3807BA5_4E793023_FA711994,
    256'hCCF5D2F4_2DAFFA84_621AB157_014B7050_9DA8413D_DA43FECD_D6C1A586_93232D1C
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h3E361D85_6AB2D1DC_6455D87F_13C9A467,
    256'h1446BEA8_56D5FBB5_4BB5B253_A70BC372_CFC9BB0A_B38A5EDA_BEE7D224_D1A66837
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h8437DD24_797B602B_068C0A1A_ECA298C9
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h6A8130AB_336462CE_E1BF8C65_3FDE5A40
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hA24DF78E_146916DC
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h1E426639_DC1903A1_7596BB0A_5B24D06B,
    256'hBFED1B83_F6A58454_49CDE17E_E8C1E710_A70D733D_F0D7A820_B8048B4A_AF6F3F95
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h283205DB_05CD6C18
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h888AD01F_E046EAFD_8BF298DB_7D5FE0FD
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h32A29689
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h5F1D0349_FD41E246_273B6DBF_7A8023D0_BC59AB14
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hBA79A60B_D0D947C2_6D8D3C38_74C6B8E3
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h4A85925C_E73B8F15
  };

endpackage : top_earlgrey_rnd_cnst_pkg
