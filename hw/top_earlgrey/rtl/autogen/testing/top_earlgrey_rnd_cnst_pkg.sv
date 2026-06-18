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
    40'h81_083AFF7B
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h9E46_C795388D_59241420_968A8450_018042D8_30E8D764_298371D7_CF45E546
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h5CD7A1A7_68B06E01_06D60EDA_0F1BC67A_DF85BD9A_56EA088D_33FFAA6A_1155AFB0
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
    128'h169AB2DE_3973D027_EE30B8F9_01F644EC
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h7CD3E56C_8ED1EC38_739F1D0D_EB7C7741
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h99CF6DD0_57F44C13_E25C7A58_77BC5242
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hE6EE63EC_DF458AE6_596E87F9_F973DB98
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hAAA29356_8FD1F31A_0165939D_819D1518
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h690E6473_CDB24793_91635057_CA1045B9_E1917E1F_F0189B04_A4F7FBA9_60FE098A,
    256'h4FB9D469_171B950E_364B0DAC_5469568E_661498FD_89197CCA_E8EA08FF_43EFC2BF,
    256'hB1C6AB5C_C63E6F47_41E80F77_7CB7FC05_041A1B89_6350C963_6D6814D2_3E2F5FF1,
    256'h275EF199_59AAA8B6_A004D557_4984DED1_CC79BD67_87D6663A_A5E62268_2A6525E0
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h83CCDDBD
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hD59C8F66_A1BB16F9_7482D9CC_DA72698F_F0A80065
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hE4D3814F_5116B3E6_F3E331DA_1182DBC2
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h9C894F18_00EDECF7_B17682D2_CE3DB9B1
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h2E1AF433_9E1F4516
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h0B546876_45F4C4AF_9355EE6D_CC76EB32,
    256'hC24B60E8_00EB2FEA_14F0691A_295CE271_0DF1A7EE_C369A1F7_B6775832_14BE3412
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hBB59B801_481ED579_3ACCFB3A_F884AE37
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h8405DBCB_5508CD6C_D2CE715E_7CCEB1BC
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h1C61B3D2_7BB8E839_8E880ECD_252956BA_81616362_B27EAFB9_03EC79BD_DF0A4F7D,
    256'hFF07DB05_DE63910E_4EE4D8A2_C7D4022F_16ED8A24_F80EEBCF_8299839C_103EAE3C
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    64'h2F18B466_6B5E59D1
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    128'h0867B85E_A711316E_5F66C0D3_86E5369B,
    256'h3288368C_62A413BB_DDAD744B_ABF2AFD1_0FF3F424_75503E63_08E01C59_6D9CB25B
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h402A8165_10C535A8_164939D9_7DF7421A
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hD4D2C18B_270D422E_C39C41F7_27D130ED
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h9B18B90E_42E4287F_60AD57D6_A551E78F_940B8AE9_F2BB4062_1F43F3AB_D8D737F8,
    256'hD12D8F43_FD1619FB_83E1A607_DCC17209_9339EF14_2E028325_714513BF_DC2A062C
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h2EB4ECDC_716A9286
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h8D2DCD18_1A4CC7F8_A1915AF6_E203CED0,
    256'h3B6FD425_FA2D8999_F9015F7A_528071D5_BBF2A214_A11CEE9E_C4F22791_1A6F0F47
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h3E5314F8_8C893A6C
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h3DD79089_A842C209_EBB51A13_5D2541D1,
    256'hBF59C65F_24BB22A9_73363BF8_05391C6D_8D0FAD7F_277BF82E_68C41562_0E7EA32C
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h0ED15052_5395F4F2_74448CDE_DEFDA430,
    256'h7A0A7CBF_AEF066F1_835FE9AC_4EE14F27_22363C00_6BA6125C_2E5DA999_B89C1B16
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h108133B3,
    256'h8A7167F8_2D4B5453_CA029357_90001030_32EED900_BB073D95_19792FAE_CDF66777
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h92489873_56407D76_5D641F23_453F6942_0B041C80_8F5F226F_3B139F84_9534634E,
    256'h5B276675_9A9B0F50_86584F53_8C2B5E65_196A6041_3C050003_7F773991_59512878,
    256'h7B208A44_5A326B4B_062F6E0E_4610476C_37621A54_253A3E07_081B7C29_122C559D,
    256'h1826610A_82174A4D_8D098979_7E97942A_578B0116_7A3D5C43_1167359E_33838593,
    256'h3170361D_96740C52_141E8881_30498E6D_68907121_2D38029C_72872499_4C2E0D15
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h084D95CA,
    256'h06120352_218C90DF_AB74299E_7882F53F_007A8AC1_BC2FDEBB_DB82764E_00B66018
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h04CEE8BE_C2514046,
    256'h12580EA9_7BFCC67F_EAEA09B2_A9CAC4AD_901BC79C_15BA3686_9177092C_56855872,
    256'h356DE28C_4B869CD4_7D6B7861_330F16A6_DD1672C5_421DF86E_EF62F1A4_FA75285E,
    256'hD5D502BC_A7E9EEF5_2614983A_04AA9DA0_613DB9A4_713A0028_0423D861_6DEB8002,
    256'hC092406B_E4B5B830_C0A98919_0D0589D0_6980F4CD_970DCC1C_385E5BA0_50C9F276,
    256'h51507558_A3E2D05E_D34782F8_44F7C0A4_6A00D623_2773FE27_A60E7A12_405C8553,
    256'hA5252190_6C0CE603_4AF25C92_93AE74D4_3BB96F69_A1606F86_E8F2A91E_9AAA76DA,
    256'h4A5C87E8_8311C847_295297ED_88791060_D669BC08_14635B49_F796C056_22677F17,
    256'hA3BE15A4_2FEAD4C2_3C2572CE_7951A321_519A3D69_9AF9F12E_5731ACCA_931387D2,
    256'h940FE3F2_A11967E2_8439EF75_C6336DA4_880C5B1D_61205951_0E50C2E2_1066B2A0,
    256'h52D240FC_A81C1180_E8748776_065A4115_1A6A2483_401008D9_BF1CE995_7E52C0BC,
    256'h46258AA6_490DD821_DFB9CDAC_2F67A24E_A2195932_ECEA77AA_D915867A_CCC2E942,
    256'h198BCA20_CF256ED2_445CC3EB_D42A564D_85B7890C_5915FC75_3A264A65_35A00F56,
    256'hF6310F03_AC8149B5_6FEA5C54_7DA38757_9594160A_41C05712_231BBA33_805CF94D,
    256'hC237036A_78214B06_88E48E7A_82EA5970_7768D53A_A64AA0FA_57144B9D_5B2DCBA2,
    256'hAB9B2AA4_A8E1C4F2_9F0D5051_1A29520E_08B81C63_CE4A4999_9D2DD792_3A058B87,
    256'h19AF80D9_65F214B8_E2B1E123_7D8C85D9_C50CC283_4EB7AC55_BAB1B878_06285916,
    256'h1A8344C2_197E1551_14F49C6F_D1292197_0EB4BCF3_450F2AAE_D98B0D85_507438F1,
    256'h0295A58C_1DB49CCB_29C9C1DA_910B226C_22D51402_52A91884_2365E132_5D08F9C2,
    256'h862DA1FB_E0D199A4_FBE8C7C7_EE85A5C3_7D41F827_17B07137_1DB10830_A3E99B68,
    256'h86D9641E_956C362A_B446DCCB_890D9498_27B08BA0_C7355E17_27D17BAC_4CAFD852,
    256'h2030389E_793623C1_2BB54EE4_0B6CEA15_314011A2_FAA11689_41066B30_1F998DE6,
    256'h35CB2324_262AD678_2A7FC1D5_0C345325_9A75959D_A1D115DE_F38626C0_AC4F6AE2,
    256'h2C495981_C717A1BD_44DFE374_F182E065_FE8B6860_88DEDB05_2389F2E9_19DF3A33,
    256'h197263E0_E563482C_D3FA69C7_011BC45F_3EED7750_1A644238_313F0E0D_29E0CD28,
    256'h8B097AE1_8497D26D_BC5E50B1_349E4ECE_C6D141C0_4F95B66A_1EEA8634_850A4ED5,
    256'h797BB318_0A714A9C_A1D12689_50260BB1_9E3111C6_3AD01647_C9888D92_DE31B171,
    256'hB52B661C_0C4A009C_79220F12_6268DE8D_15A3515C_80B1B74C_A96C144C_62F0ABEE,
    256'hA7C09D92_1EE04903_911349F6_3B2B80A9_74E5056C_F2D26EAC_DB9405C4_04044945,
    256'hFD1014CC_188053D9_29B51242_6C95A947_9DAFB3E0_B709C7E1_FDA81595_DB12425B,
    256'h1A920A54_091A36ED_244E5C05_0DD63F48_A06E612F_ED101DAE_6B489B18_2237EDF8,
    256'hF5E9772F_40C5376D_AF70F8CE_660AD41E_BCB58E19_07006CC0_392A93B7_2B0AE91D
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h6289EDD5,
    256'hF001DCD4_095890A2_90A9B632_F0395D11_CAC7F7E9_E764ADD7_EDE232A4_E00DABF1,
    256'hD1D2AD2E_2A5133F6_A12FF2EC_1569BEF1_F0B924C4_70AC5A99_809985DC_415BA1EA,
    256'hCED382D5_4C9E378D_030EA5D3_7665D43A_035F4EA1_E463032A_3A8E24B4_547F8B0D
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h0F26D18F_C86EF733_E0574E44_67BD8D0B,
    256'h7306EA64_9EF974E8_50588BB5_061A2AF9_E51D6ADC_3A9238D4_0AB007F7_4991FC6C
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hA69F03F5,
    256'hA88525A5_87CEDEA9_0913BBCE_814E6794_DF2BDD99_E66D0780_1B027BD4_E9BF578B
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h04F22173_C8F0BD8B_B254BE88_D77C0EC4_522FE26C_27CB1E12_A13BFA0F_A0A33CDB,
    256'h4F6D8F4A_BCD0C2C6_ED295C91_DD00A202_78153A33_69F5D610_3FFCDA5D_90EE9963,
    256'hFDD5E495_59AB6E25_390942C1_D2F196C0_ACC9B606_CFE85A9A_1BDCDE11_16B708F7,
    256'h74FE9CD8_8E34C3EC_26D420EB_1F8D7E5F_B0EAE1B1_D3184035_984C5176_E3059203,
    256'h2BFBB8B5_8987AE37_F624CD8A_0A720B53_F456F9FF_67137F55_64CE851D_F33E1CAF,
    256'hB39386E6_3D419DDF_C54B0157_BB62842D_941971E7_30D14ECC_7B8070BF_4D17D91A,
    256'h5BA6C78C_9EBA66CA_387DE583_A5F86A2E_AA798197_7A22B948_2AAD2C9B_A407A750,
    256'h5832280D_E0774323_EFA9319F_4765B475_45A84936_E90C6844_5E468260_6B616F14
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hCACAEA4E_16EF75A4_823EE1BF_100B50C3
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hA2C1BA79_A60BD0D9
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h47C26D8D_3C3874C6
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hF901836E_0753A55C_C7F7C8B1_79828835,
    256'h1DD932AC_3B58FD7F_B09D1A7E_BA027259_F2BCBD84_040B7A99_41633B95_E4852E2E
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h38CCA5A1_C161125E_4333F5DF_1EC9BBD7_E9800AD5
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h650A85C3_0237536D_C3E35040_DE9AC1A6_F2B35C99_FB71E1AA_AB3C2083_83ADF503
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h11FF71FD_46921923_A8CD8C6F_F98F9BDF_C2B205D8_690DD355_00E5A51B_BA34A71D
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h81E9EB87_6B6F1996_B2BE4B58_DFCFB830_B9E25BDA_A3E1AFFA_91806D01_A89BDF50
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h84C3F043_FE74B4FF_850B4A6D_EA97774B_63EF1E13_CA69B8BB_7DAE3157_B7279A2B
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hD0F45178_ADD4099B_463A9BFA_DEB0A249_E67A25FE_EA95E50B_27DEDC68_15C375B4
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hBD85E84A_EB69C3F4_DB751585_B16ED45D_55A6C1FF_D5C92099_CDEEA949_DC968AC7
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h0991C551_4057A6A1_5FAA5773_95193CDE_4A6705BD_11203330_A927A8CE_1AC88224
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hA441C419_2ABE1DC4_26FEEE2C_9B1C8B34_B1A821AF_E522E11C_4049D9B8_5F9DC3C9
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h9A378685_79B46A84_095EA981_140FF7F0_C4AD73D5_9726774A_37E33560_266D52A2
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hD9C49012_61C19F48_0238C019_7CFA2C90_10EEFDD6_6D4B9172_5B5E1A95_A1411451
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hC3DA5967_F2CC89F1_B0ECA338_8F277FFA_E4319B41_44B76B7C_902A9C89_F6F8F885
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h6D8B76B9_B8EC2F4F_0EAE6D9D_26C47E27,
    256'h9080DD58_BCF5AA54_A3F54824_B5C6538F_8AAE68EC_24DF2D9B_070658CB_5B072BB7
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h4E79DEA4_7A41863A_DAED04A0_43653AFA,
    256'h5748AEFE_46B7A519_5322D57D_74AF0790_F5050E13_43B18DDA_6827D474_657B77F7
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hEDA1A070_47F93705_1A057461_414B8B35
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h87C6DE71_B922084E_C4EA31A9_7E0ACB1A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hCB48CBA0_1DEA8881
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hAEEB6870_3F4AD056_8981DB29_1BBFD6E4,
    256'hB953D781_D5CC1CA6_DF686A89_839E03AC_579CC508_0BC459F9_28EF1244_0F7CDC1B
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h73F6EE87_0F58B89F
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hABFE08C8_27837C78_67EEC58F_F573DB5A
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hAF6E9564
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hED7EB8C8_56807CD7_6473460C_A3D2FC60_36F29349
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hF893C20A_2865EF55_E0A6E7A0_BA0B1C29
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h6731C59D_861E3633
  };

endpackage : top_earlgrey_rnd_cnst_pkg
