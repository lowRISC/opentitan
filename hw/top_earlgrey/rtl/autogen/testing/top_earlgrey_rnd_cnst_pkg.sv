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
    40'hE6_596E87F9
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h6E58_9D685860_3D61C92C_462744A5_D47C838C_04D0C279_04D26401_A356499C
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h4FB9D469_171B950E_364B0DAC_5469568E_661498FD_89197CCA_E8EA08FF_43EFC2BF
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
    128'hB1C6AB5C_C63E6F47_41E80F77_7CB7FC05
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h041A1B89_6350C963_6D6814D2_3E2F5FF1
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h275EF199_59AAA8B6_A004D557_4984DED1
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hCC79BD67_87D6663A_A5E62268_2A6525E0
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h83CCDDBD_2A1B0080_57C22C88_4ED49D87
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hA5B56BA7_353C5321_42F50667_E220C5B7_24C3FDB6_D060653B_42A96F88_B574E4D3,
    256'h814F5116_B3E6F3E3_31DA1182_DBC29C89_4F1800ED_ECF7B176_82D2CE3D_B9B12E1A,
    256'hF4339E1F_45164A41_8EBC5221_0D58DC65_508E869A_F565C1B8_7D687EE8_37FC119F,
    256'h5BBE7395_CAC38919_C27006C2_3E142591_0840042A_75ECC25D_4E2267E3_BFF26E00
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h3AACBF7D
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h13CC9759_93DE297D_46B0CC88_51F1BEFA_C28074EA
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hCD6CD2CE_715E7CCE_B1BC1C61_B3D27BB8
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'hE8398E88_0ECD2529_56BA8161_6362B27E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hAFB903EC_79BDDF0A
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h7AAAECC2_51DD554E_63EF872F_34838ACF,
    256'hE31142E0_9287CD29_6D65DA64_6CB53C49_ED9A0E89_8852C0C6_8FC3918D_FDD817D3
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h5C0CAE7E_D7FE6C45_D1534FD3_90C7B068
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hCFE89687_94DE88E8_FF4ADC3D_02EBFA0A
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h1D5FAA5E_E00CA534_911723E1_EA068740_2A816510_C535A816_4939D97D_F7421AD4,
    256'hD2C18B27_0D422EC3_9C41F727_D130ED9B_18B90E42_E4287F60_AD57D6A5_51E78F94
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    64'h0B8AE9F2_BB40621F
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    128'h56869361_988CC8F1_EB9B97E5_537227B6,
    256'hE5DE0FE4_BAB1B756_87DC4A11_1BC9CC0E_3B3A409C_C01A6018_5FE32F43_75DAAF10
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h40CA72CE_50C55920_BA14E126_DCD0A3F6
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hC9B71D03_E571BEE0_E47E5B49_E80E3DA3
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h9A52777D_BCFD9E38_D4D189EC_4B433E53_14F88C89_3A6CB3FD_30A87C38_225A1510,
    256'h8E992D14_BF1225D4_B19B23F4_0E358F1B_F4FE1D5A_50B10232_A8B3C33A_6017B970
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h36561AA2_62310424
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h08F2BE5E_F95BAC55_48A33487_42170E9C,
    256'h647700D6_133099AC_ABCC72E9_A2E4520D_1E8E27C4_FF5C2EDB_DB690F85_9977BE41
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hD66B5813_54CBCB9A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h7BE94F37_F4088F9C_141F8743_4554E6CD,
    256'hA61B4AD9_3428915F_F5CF2BB8_4B0B5C08_B71B282A_A3AA4286_FD8C056E_E7D59C4E
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h7FA5F85B_1AFF0915_4166EB3E_D4AA3D60,
    256'hF404A6FA_BCD06D9E_372E5D0D_41478A03_128DB6A4_97B9F320_B3ADDC04_DC866270
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hD8582552,
    256'h6737C611_FA0E7D75_4AE64A35_4CC7C16F_A06AE28E_208C1D5A_FC5F0D9D_E8D61CC3
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h5B671E8F_6A9A7218_5A85382F_120B4992_1C069811_7B91909F_4E524C36_43762C94,
    256'h47587732_196B1D35_2A0A5481_15995053_1B443982_8A7A782D_93591334_8B7D5131,
    256'h37230C30_4B273B9E_898C6100_1F41634F_757F4846_6C9B0109_034A2604_3C627197,
    256'h253D079C_05695C7E_248E732E_107C2B57_6F42885D_5614705E_744D5508_0F96283A,
    256'h2186953F_683E0E33_22178D80_5F647960_836D1602_0D846E45_1A874029_9D666520
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hB4592FF1,
    256'h9842D516_06FE22B8_ED0E3F50_759650EF_701A4E6E_4916EEE5_6EF868E4_092F9516
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h30A2887D_19A2CB9A,
    256'h171B18CB_3951EA60_EDCB28D0_31A948B1_626E2A58_6C97C193_EA12F357_C4EC5E9A,
    256'h69186A0C_D66F8E76_55E4A881_D5D1D11C_9E13A6D3_9F22311D_6E5983E5_349C0615,
    256'h77081319_1E5408DA_5443B01E_9189CF65_0AF28A44_21E5D799_6EA6EEF1_29C50B7A,
    256'hBAC38171_85AF260C_520DFA4C_C903FE88_0665C306_D9B60CA7_6DD2002F_F41A2A9E,
    256'hED41B681_5C2141CF_1E641EB8_0D368922_D9481E2A_A1523173_AF5B5A09_DE86604C,
    256'h55108792_5AB8328C_A7021149_BBA3A0C6_866A8E81_ACA3018B_5B6C8F6B_4020BD8B,
    256'h7398430E_5799A451_DEC21803_78982A66_E1046DD5_55915AA1_FF52DEDB_6961006D,
    256'hD47ED04E_99C6B2D5_1E8541A6_0D77D6B7_B08A07D4_3AD46FB2_2C04F678_90DB2B5C,
    256'h5DB383A4_1302582A_76685E2C_4053F213_C3D0D06D_D8AFCAF8_3CD57CA6_F9C60059,
    256'h169A7455_3B8A891F_0421A9B1_B8229FC4_38F00D3D_EE1020D9_7650E605_8C4B5356,
    256'h08F5AC55_84A4A142_1E27F00F_8C2554AE_B2344922_0589A7DC_60963FAA_716A3051,
    256'h7D8F02D8_EF012672_FD75AD19_95E00B2B_5CD3F5C7_9922B21C_8B6B988B_A0BD85C9,
    256'h3A5C65A7_A682ECEA_8D98A895_45928CC2_E96F5486_62F2AD4E_4CF255EF_2445C5FA,
    256'hC6339CF4_2A779E60_951A1A43_1B663E21_C3099299_7A7703D6_7DC143C0_EBD0527D,
    256'h4CBB34E1_1F6F81D5_DD72A052_90709184_8BFB1F95_A1C4CA74_6C476371_725A211B,
    256'h14214B06_89048E3E_82E70DA0_C61B7804_204AA2EA_EE924BB0_1781189F_AE5BDACC,
    256'hB2DA6BBD_3CB1C356_4D0511A4_95226938_24E071C5_392B783A_98AE42C6_52ED96C1,
    256'h62E11DC2_25A7317C_8CF13B90_7893D23C_64C85DA5_F0CC2834_D97B8E8A_56DC8702,
    256'h6B6EAE07_E22F85A4_D8D5161A_8344C1CB_C2E73554_453D295B_F44A4868_03AEF59D,
    256'h52F3CF10_450F2B5B_05930D8A_907438D9_8295D069_65031D27_6594E4E2_317DC582,
    256'h804B5505_B15D1E76_AA37EDA2_6FC36AF0_AC0FE391_89F436EA_67C53788_2993989F,
    256'h45E63132_EB614880_C0E279E5_9C70DFB9_D53C502D_BEAAA4C5_00468BEC_285A2504,
    256'h1A3CC07E_687798D7_2C8C9098_AB59E408_2A8E7A55_07585325_9A75959D_AB1115DD,
    256'h24862909_4C2B13DA_B8890756_6071C5E8_6F5137F8_DD3C60B8_197FAF9A_182237C1,
    256'hC148E2B8_C68677CE_9600DC98_F8399616_3482F9B0_4FE9B28D_C341168C_5F3EF037,
    256'h501A6442_38313F0E_0D2A70CD_288B097B_118497D2_6DBC5E50_B1349E4E_CEC9E9B4,
    256'h504893E5_6D9A87BB_458D2142_93B55E5E_EDF602C3_52A72874_49A25409_831DA859,
    256'hE3111C63_AFCAC059_1F262236_4B78C6CA_8171C02E_261C0C4A_009B9922_B483CAAE,
    256'hCF4989A3_7A34568D_457202A4_EB674CA9_6C1446CC_24ABEF07_C09D921E_E0490391,
    256'h1349F63B_2B80A974_E5056FB2_D26EACDB_9405C404_044945FD_1014C8F4_8053D929,
    256'hB512BA50_9B26F7BB_3095A947_9DA613E0_B709C7E1_FDA815B1_2576C490_96C6A482
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h740A7CE7,
    256'hC92A49F7_1747D5A7_E3B7E444_732A39A6_9F03F5A8_8525A587_CEDEA909_13BBCE81,
    256'h4E6794DF_2BDD99E6_6D07801B_027BD4E9_BF578B14_6F616B60_82465E44_680CE936,
    256'h49A84575_B465479F_31A97523_4377E00D_28EC32FA_5850E8A7_F607A49B_2CADE12A
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h375A21BC_7D010BBC_D4CA2458_D8900A6C,
    256'hC4159ACF_43FC490F_E7EC5CAD_31465AD8_E767039F_778A5768_BABA8257_88B92DFC
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hB2D1DC64,
    256'h55D87F13_C9A46714_46BEA856_D5FBB54B_B5B253A7_0BC372CF_C9BB0AB3_8A5EDABE
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h0F265907_E8B6C14F_5711C345_E3BAA8CC_74FA5E71_218DAD7E_AEF10020_8F0DE56B,
    256'hBED4D95B_3B4387F5_CBC52D78_96E229F4_FB90ED95_2AA4C2E4_1B66A9F6_481963B8,
    256'hBC4E3D15_72B75635_3E503867_39B5177F_9B580903_012F4C6E_CD47F8DA_494225C4,
    256'h761C1E91_36FEBDB2_533C80F2_5161A097_C6BB70B1_41523A77_0BAF757C_DE4B12FC,
    256'h5D9DC09F_9E86040E_92D39AA3_CF995FB9_B4461F8A_88186CEA_05A528D5_DCD61D02,
    256'h93082E54_D732DB8B_FF83D0F3_44ACC827_E994C7DF_A74A7313_857DE6D8_F02334B0,
    256'hEE9CB30C_5C31CA6F_F77AA122_2C821089_AAE06DE1_55166914_8E4DEB40_5A3F65EF,
    256'hBFCE6264_33AB3081_6AC998A2_EC1A0A8C_062B607B_79FDDDF9_843768A6_D124D2E7
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hA6F2B35C_99FB71E1_AAAB3C20_8383ADF5
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h0311FF71_FD469219
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h23A8CD8C_6FF98F9B
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h20A733FE_35C48BE4_587532C5_ACF642E6,
    256'h7B5EC722_7CAA639F_414EFDBE_4A0C5929_786FA860_1F536E1A_9015D036_B606CC37
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h1F75401D_1BCC54C2_CCCBADED_8FC1C26F_83223F89
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h57A6A15F_AA577395_193CDE4A_6705BD11_203330A9_27A8CE1A_C88224A4_41C4192A
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hBE1DC426_FEEE2C9B_1C8B34B1_A821AFE5_22E11C40_49D9B85F_9DC3C99A_37868579
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hB46A8409_5EA98114_0FF7F0C4_AD73D597_26774A37_E3356026_6D52A2D9_C4901261
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hC19F4802_38C0197C_FA2C9010_EEFDD66D_4B91725B_5E1A95A1_411451C3_DA5967F2
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hCC89F1B0_ECA3388F_277FFAE4_319B4144_B76B7C90_2A9C89F6_F8F8856D_8B76B9B8
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hEC2F4F0E_AE6D9D26_C47E2790_80DD58BC_F5AA54A3_F54824B5_C6538F8A_AE68EC24
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hDF2D9B07_0658CB5B_072BB74E_79DEA47A_41863ADA_ED04A043_653AFA57_48AEFE46
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hB7A51953_22D57D74_AF0790F5_050E1343_B18DDA68_27D47465_7B77F7ED_A1A07047
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hF937051A_05746141_4B8B3587_C6DE71B9_22084EC4_EA31A97E_0ACB1ACB_48CBA01D
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hEA88816D_C0357C3D_419213EE_BD8FED49_C167447D_0A22FBFD_5230D29F_B8E5B65E
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h7C4102C3_7BC6A838_63A98A9A_7F84EA7C_2377F98C_F20CCAAA_3BD0E4E0_2590E09C
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h975C71CA_965F7B31_6D6C12EA_819870D4,
    256'h51DC29EE_296DA185_0BE6BED0_73F6EE87_0F58B89F_ABFE08C8_27837C78_67EEC58F
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hF573DB5A_AF6E9564_4DFAD426_2A7ADB7F,
    256'h05D963E4_282AE9DD_B8FBE7A1_38D956AC_336341A5_36F70C3E_E90CAEAE_11CB84B6
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h5FDC5C70_2578F9F8_93C20A28_65EF55E0
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hA6E7A0BA_0B1C2967_31C59D86_1E3633E7
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h5586C29B_02CB9DE8
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hEF969056_42C5E12B_25C9F6FD_9D65E82A,
    256'h912252A8_4347380F_FC70B7C2_E63ED0E7_094D9F2D_D71EB676_3BCC9801_AB20178D
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'hC752A9C4_607CEC7D_CA3EB5F3_D09295A3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h2C9CBAFE_5EFF3CF3_5156B781_5F112BB8
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hBDC22909_AD6A99CF
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h7126AE21_3C3C463A_2FDAC6C4_34518BD4,
    256'hCCF1CA29_960277C1_5255691D_8FB47612_B7FFDB79_ED0ABA39_9E0F5EB7_A00C2264
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h9E648FB1_0EE6F51A
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hC4FCDB4B_8F96F977_53B0A824_7424B489
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h90156C71
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h3D59FD39_6DDF262F_01E81961_D50629BD_2D8C9246
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h8CD14C0F_2E129D94_3ABF68DA_18DBF422
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hA9EBB7EB_AF19BE85
  };

endpackage : top_earlgrey_rnd_cnst_pkg
