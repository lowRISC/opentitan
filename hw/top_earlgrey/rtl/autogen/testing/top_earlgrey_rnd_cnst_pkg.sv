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
    40'hB8_7118AF11
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h3DA3_8428D1D7_2C69C98E_24203015_5F6E4461_99408565_34800DD2_1695871E
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h85BD9A56_EA088D33_FFAA6A11_55AFB016_9AB2DE39_73D027EE_30B8F901_F644EC7C
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
    128'hD3E56C8E_D1EC3873_9F1D0DEB_7C774199
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hCF6DD057_F44C13E2_5C7A5877_BC5242E6
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hEE63ECDF_458AE659_6E87F9F9_73DB98AA
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hA293568F_D1F31A01_65939D81_9D151869
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h0E6473CD_B2479391_635057CA_1045B9E1
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h917E1FF0_189B04A4_F7FBA960_FE098A4F_B9D46917_1B950E36_4B0DAC54_69568E66,
    256'h1498FD89_197CCAE8_EA08FF43_EFC2BFB1_C6AB5CC6_3E6F4741_E80F777C_B7FC0504,
    256'h1A1B8963_50C9636D_6814D23E_2F5FF127_5EF19959_AAA8B6A0_04D55749_84DED1CC,
    256'h79BD6787_D6663AA5_E622682A_6525E083_CCDDBD2A_1B008057_C22C884E_D49D87A5
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hB56BA735
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h48B6F5CC_D4F0C25B_CA307379_FAEB36C7_58041147
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hEDECF7B1_7682D2CE_3DB9B12E_1AF4339E
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h1F45164A_418EBC52_210D58DC_65508E86
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h9AF565C1_B87D687E
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hEEDF1F32_34B462AE_144607AB_F6E0DAFB,
    256'h5DCBA6C8_47A3F995_3806D921_35DD2B14_0290914F_CC1E761A_2C3295CB_D69C437A
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h378405DB_CB5508CD_6CD2CE71_5E7CCEB1
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hBC1C61B3_D27BB8E8_398E880E_CD252956
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hBA816163_62B27EAF_B903EC79_BDDF0A4F_7DFF07DB_05DE6391_0E4EE4D8_A2C7D402,
    256'h2F16ED8A_24F80EEB_CF829983_9C103EAE_3C2F18B4_666B5E59_D16C252F_9DB7F094
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    64'h161D818D_C161FE26
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    128'h853EC21A_35348B23_31141F4E_C07B1167,
    256'h998D5AAA_DE24ABC8_F9FDD70D_C82D6BC6_1297AFE8_BA9D4B10_FCE76D09_36755E00
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h816510C5_35A81649_39D97DF7_421AD4D2
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hC18B270D_422EC39C_41F727D1_30ED9B18
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'hB90E42E4_287F60AD_57D6A551_E78F940B_8AE9F2BB_40621F43_F3ABD8D7_37F8D12D,
    256'h8F43FD16_19FB83E1_A607DCC1_72099339_EF142E02_83257145_13BFDC2A_062C2EB4
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'hECDC716A_92861FF7
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h359634CC_6AF8FE65_4C8E44BB_1C1E8B3C,
    256'hEA43821B_768825FC_DF1BD015_F7A52807_1D5BDFAA_214A11D6_E9EC4F22_7911A6F0
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h8C893A6C_B3FD30A8
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hA9B75048_AD734645_E2AD9C13_3C26A197,
    256'hF0777B1B_74A209E9_C95B9CD9_8F8C014F_071B9343_F78B09EA_FECB9A31_0558839F
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h51EDCE57_F6FA0D1E_C8A0F27E_0501B57E,
    256'h994C9C7B_6BF4A90B_D05CA0F3_35AEC381_2F853E5C_8AC363D8_06B19984_9709976A
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
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h47C26D8D_3C3874C6
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hF901836E_0753A55C_C7F7C8B1_79828835,
    256'h1DD932AC_3B58FD7F_B09D1A7E_BA027259_F2BCBD84_040B7A99_41633B95_E4852E2E
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h38CCA5A1_C161125E_4333F5DF_1EC9BBD7_E9800AD5
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h650A85C3_0237536D_C3E35040_DE9AC1A6_F2B35C99_FB71E1AA_AB3C2083_83ADF503
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h11FF71FD_46921923_A8CD8C6F_F98F9BDF_C2B205D8_690DD355_00E5A51B_BA34A71D
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h81E9EB87_6B6F1996_B2BE4B58_DFCFB830_B9E25BDA_A3E1AFFA_91806D01_A89BDF50
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h84C3F043_FE74B4FF_850B4A6D_EA97774B_63EF1E13_CA69B8BB_7DAE3157_B7279A2B
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hD0F45178_ADD4099B_463A9BFA_DEB0A249_E67A25FE_EA95E50B_27DEDC68_15C375B4
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hBD85E84A_EB69C3F4_DB751585_B16ED45D_55A6C1FF_D5C92099_CDEEA949_DC968AC7
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h0991C551_4057A6A1_5FAA5773_95193CDE_4A6705BD_11203330_A927A8CE_1AC88224
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hA441C419_2ABE1DC4_26FEEE2C_9B1C8B34,
    256'hB1A821AF_E522E11C_4049D9B8_5F9DC3C9_9A378685_79B46A84_095EA981_140FF7F0
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hC4AD73D5_9726774A_37E33560_266D52A2,
    256'hD9C49012_61C19F48_0238C019_7CFA2C90_10EEFDD6_6D4B9172_5B5E1A95_A1411451
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hC3DA5967_F2CC89F1_B0ECA338_8F277FFA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hE4319B41_44B76B7C_902A9C89_F6F8F885
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h6D8B76B9_B8EC2F4F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h706FB310_EE91C18D_B25CD085_FECA6164,
    256'hC79D0074_08E6EF4F_4CA977D7_C0662F46_A28D4B78_4A856ABD_6824EDFC_499DBAC3
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'hD474657B_77F7EDA1_A07047F9_37051A05
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h7461414B_8B3587C6_DE71B922_084EC4EA
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'h31A97E0A_CB1ACB48
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hE2BAB79B_975A58A1_83A4527E_F0BC6EF6,
    256'h507B87F7_33D53B55_60E780D2_C5E73142_02D91652_8EF12440_F7CDC1B8_22E87A32
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h29EE296D_A1850BE6
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hBED073F6_EE870F58_B89FABFE_08C82783
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h7C7867EE
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hD1BC70DB_288506AE_7C5DB826_F2912C93_6ABDBA38
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hE90CAEAE_11CB84B6_5FDC5C70_2578F9F8
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h93C20A28_65EF55E0
  };

endpackage : top_earlgrey_rnd_cnst_pkg
