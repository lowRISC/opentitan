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
    40'hDA_F5141DF1
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h2D14_0549D5CF_11F0CD25_B04C94E1_E1608664_0A37A09D_54C60145_9A70A8A6
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h0D857783_4CCC6CAA_A63A8E66_04338151_B9A23C08_F9EED04C_A1EBB0BD_D305FFB6
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
    128'hC4818054_E0E0EDB0_ACD0B040_FC629EA7
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hF8B17FA8_8FEE02E3_F0864223_A2E23A8C
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hC31E2DE5_E578D43D_2DCE49E3_60CFB594
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hACDDF170_684F6EAD_2B7FEBFE_895523D7
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hBC4846A4_85956C7F_904B9EDE_D09B89A7
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h5433566F_4963D9DC_27F3ECB1_1CE3B87A_AA7ABC85_920B1881_083AFF7B_DE18EACF,
    256'hF8567945_3DA77D92_A176B871_18AF11CD_BE78D670_60615A20_B9C0740F_07969CCD,
    256'h2D10A1A6_E7988FA5_28AC032E_0A6138CB_8316FF95_C65CD7A1_A768B06E_0106D60E,
    256'hDA0F1BC6_7ADF85BD_9A56EA08_8D33FFAA_6A1155AF_B0169AB2_DE3973D0_27EE30B8
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hF901F644
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h903E6BA6_C282D992_D49456D1_8F047371_E2DE69FD
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h87F9F973_DB98AAA2_93568FD1_F31A0165
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h939D819D_1518690E_6473CDB2_47939163
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h5057CA10_45B9E191
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h92130429_C46B27BB_E752CD20_00F3BAE4,
    256'h8B7E6CBA_1E597DDD_436FF0D7_1663E325_7348D0E5_F456AE4E_2098AA90_661BC1DF
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'hF19959AA_A8B6A004_D5574984_DED1CC79
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hBD6787D6_663AA5E6_22682A65_25E083CC
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'hDDBD2A1B_008057C2_2C884ED4_9D87A5B5_6BA7353C_532142F5_0667E220_C5B724C3,
    256'hFDB6D060_653B42A9_6F88B574_E4D3814F_5116B3E6_F3E331DA_1182DBC2_9C894F18
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h00EDECF7_B17682D2
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h2BBFAB6E_A4E027AA_55FF9797_D65C4192,
    256'h20B700E7_7DD98E34_72D10DA1_A7FC9A1C_B06560C8_52F8D048_54479CC1_8BB2E3F3
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h01E9EE42_0D5B523F
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h83B8A60F_C508664A_AD97D2E7_7714CC43,
    256'h9144A2F4_698CFFF4_6307D771_B0950763_6B87339E_1D2FBA5A_EB3824AD_771B201A
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h07D75E55_0EECC237_EA729932_954DC285,
    256'h334848E2_BABCC611_F07E2DF9_B5976991_BFBAB3C4_9F49A0CC_326214B0_35C68DB9
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hD7FE6C45,
    256'hD1534FD3_90C7B068_CFE89687_94DE88E8_FF4ADC3D_02EBFA0A_1D5FAA5E_E00CA534
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h78867A54_4B3E4450_59196D6A_5C759B46_6E246962_8F26809C_488C512B_11025F84,
    256'h3A2F8599_1D4E4F56_5B4D3D66_00072D9F_583C8A4C_71779A33_64326F3F_791F1E25,
    256'h1476633B_2C7E3796_299D8813_0834367C_4361955A_5E709715_09223812_67019E0A,
    256'h1C930492_98035389_0C0B727B_94681B82_6C55210F_31205D74_45054A47_7383526B,
    256'h57607F28_8E0E1830_8D412E90_0D278B1A_427D3949_16351065_812A4087_06231791
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h50B10232,
    256'hA8B3C33A_6017B970_36561AA2_62310424_04E5EF74_645BE00E_A5B567DB_B5DABAC0
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h7C88FA95_BD35ADFA,
    256'hA50F8C25_7AE05F4F_47BC2DFD_52C77BC1_1DBB9712_9C52AC51_0C0EE676_6D81556F,
    256'h5A245B55_B39FE08B_5B066A27_5C42437E_544A5A90_87E4C1BC_2C74E618_622148C7,
    256'h453109A8_8D44F26D_5F7143C8_9327DFB5_E44B781C_04C66830_1BC6DCE2_B7003A48,
    256'h0592EA70_951760D0_2A0DE2B8_E198D0C3_760149C8_8B41CD27_C4EEB44C_DAB157BD,
    256'h6BC63505_3F8F1430_D561A5A2_76157B1F_E7A02037_5E184E63_7A6BA006_775C97F2,
    256'h8D559484_435D7306_CA193D7B_99E8A6D2_B4260859_C1B5191D_EA01437F_C290F066,
    256'h5B196A7E_04803028_A95B5486_B841E492_678362A4_849F77B5_DF6FEBB5_E997BE4E,
    256'h722430BE_DAE5ACFA_25120019_C11B9CF0_5E7E73B1_7942B694_E5D07111_A2582838,
    256'hDE450D06_16419230_0C300E6B_580AB592_9AE94B90_B63050D7_2AF79EDC_61CA653D,
    256'h0CAA209A_76E9A712_3519D451_C45CBA2B_F9F2DD76_91F6687E_01EAB009_CC1A0043,
    256'hC0091302_F70EA13A_2241898C_ACDB8888_B4998AE8_154F2591_549DD22E_14D5D704,
    256'h36E6C0A2_A3500E62_42560F8E_A6517880_6C5832DE_98165045_35B4099B_6912B32E,
    256'h162167B0_6E5489A9_37E82956_9B5180B3_8CF82308_D85CAA7C_0E9770ED_1F71D2DE,
    256'hF6A4549C_79A310D1_E4EF1C0E_A208EB01_371C2498_137D95A4_D02DB808_016B1857,
    256'h5FC8F5EE_031182E9_7057841B_AA444FEB_7C3DFA06_104AA901_7746D78C_324DE936,
    256'h1251B4CC_2B197490_A3351EBD_26E739EA_0FBCC503_127DC562_5BD3094A_A020D4AD,
    256'h2C1EBA9A_86C59F89_396D1F02_E2E6D936_497B8A3F_63A11541_B6C7DA73_FCB108D8,
    256'h7BF8B2BB_57C58713_7261A3F4_E57D0169_90A6AA2F_D666D791_9D64725C_3DDBE15A,
    256'hC70C5810_9AF88283_F4B9AA8A_091A3C47_42B0A3CD_778E5A28_DE23640D_A421C8C1,
    256'hECE58991_B08ECBAE_1CBC627B_26312CDD_43452CAC_2D4210C6_4023C59A_5F8FAB2A,
    256'h56FAB001_EB209E73_5A58B4CC_B10A44E8_78A66DB2_AD1A3D4F_B9C48355_81D324A0,
    256'h57D93320_8AB0E5B1_8C5D1B2A_02B28E0D_CEB8D89C_09EAF13A_2E7CEB50_54769D21,
    256'h621A26B3_ECB419EF_690701FF_1B4E6FC0_7C606C2F_F1140056_46AB9EF2_80D295A5,
    256'h426C58F4_0C2A6291_32A71991_DE602A38_2A11B126_4A33F0E4_B62C9AAE_916DB91A,
    256'h659AF838_1610B592_584658BA_3558091B_2A10191E_5BA3862F_3914175C_AF439545,
    256'h28571781_208B0D86_DBB18538_824BF7A8_FC82E797_42325204_84D8398A_D2F0F42B,
    256'h48481570_A2C48467_469C682E_F3E43B22_2545F9E5_834590D2_6945B088_78A5A159,
    256'h51CC361D_482A0533_4A12B7D6_D2255763_1F052F66_E129AB5B_AB903F11_239AF670,
    256'hC5022CD0_CC511EA0_64923B68_65E71C87_38130874_924C8BBA_5C54674B_E194F6BB,
    256'h0CB1031A_935512D5_9F8A4CE1_08BC0369_8ABA87A7_A1404163_9D99B3BD_53580533,
    256'h4E07A318_99884F72_D3E716CA_699AC9BD_25085D56_781A5AA9_D9028B53_9E713598
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hE0895D76,
    256'hF862EF81_F419E3C6_CDC8662C_71EAC141_666E443C_6492D9BC_F7A82420_750E5DFC,
    256'h5E3ED4F2_907532E1_79EBEC7E_D7D3A5EF_4982F73E_D91C4B1C_D0C85EC5_E548B401,
    256'h84A69EB1_E5439646_0E36C55C_459EFE9E_43836FE8_78E46433_7EBCAE32_38DCDF7D
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h0B325F95_B999ABB7_91AF9530_1B78DA72,
    256'h94E11483_2E8033C7_59061DB3_4F6803F5_F62CDCBE_927F04C5_23B5BCAE_01B558BA
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h5A54FF19,
    256'h343CB320_40B34907_68889D27_E0BA8588_D34C05BC_F127DAE5_8B65D6A2_51088099
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hC115938C_D4A11DC9_F317B8B0_72122379_F24D6C4E_C52D8263_7327FDD0_DA53E7A0,
    256'hD764F513_AD461021_3C208899_39EB09BB_A6A4B9E8_A39B140A_E66DD95A_8FF6DDC2,
    256'h45327FB5_1C702C75_7BEE3126_68DBD561_CA57BDC4_36E4CB9F_418D34EA_16BA8E1E,
    256'hB23FE36B_A9F07698_E08719FF_BC80664B_8BED4233_D690F7A5_3E187400_DC11355B,
    256'hC006963D_022F240F_D22BEF77_6037E22A_04B4BE92_8558A7F8_014CE90C_C80B9AE5,
    256'h5469AA28_52C38A1F_AE486F40_7C4FABC7_255D3AFE_D12E945E_FC05FBAC_1B6259AF,
    256'hD367296A_0E55A865_44869EEC_22430D08_DFD8A289_8197B7F1_F43B7E7D_CD38CE56,
    256'h5C6E3091_C67A9D4A_7851FA49_E1509CB6_83BF4784_F9DE035F_951ACFCC_B10771B3
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hA4D3D738_71FDAF5A_D0C1DD1E_95F99D71
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h29CA6861_A4425B9C
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hC42EDBA8_8A15B752
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hB63956D3_1AC318F2_3C2C7EDA_DA2E28CB,
    256'h781E5EC0_55CD943F_26100EA9_CF9117D2_9F0B548D_4FAA5B11_D60CBF09_26E6E9D4
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h85E8B7FA_3BFA8A31_0247D131_C9E59672_2A93742D
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h227A9781_79AA2E6A_DC5EA5FD_83777D38_7766BA9E_8C77A65B_1AAD174D_D41ACA70
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hD3807BA5_4E793023_FA711994_CCF5D2F4_2DAFFA84_621AB157_014B7050_9DA8413D
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hDA43FECD_D6C1A586_93232D1C_3E361D85_6AB2D1DC_6455D87F_13C9A467_1446BEA8
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h56D5FBB5_4BB5B253_A70BC372_CFC9BB0A_B38A5EDA_BEE7D224_D1A66837_8437DD24
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h797B602B_068C0A1A_ECA298C9_6A8130AB_336462CE_E1BF8C65_3FDE5A40_A24DF78E
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h146916DC_55F8CE6D_BFAAD089_10FBE182_2C22A17A_376FA131_5C0CB3C2_9CF4D10A
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hE5C8F0C7_B034BF23_C9068E30_7D8513B7_734AA78C_C36F947A_2737BBC0_ACD1447B
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hAA83C3FC_818BB3B4_A840AD32_14CEB3F3,
    256'h54CA2E08_9302C3EE_1D695AA6_16283205_DB05CD6C_18888AD0_1FE046EA_FD8BF298
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hDB7D5FE0_FD32A296_89A0C154_9C28C210,
    256'hC01FF7E6_E6D20E04_04E7B51D_020AA369_5DF42597_CACAEA4E_16EF75A4_823EE1BF
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h100B50C3_A2C1BA79_A60BD0D9_47C26D8D
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h3C3874C6_B8E34A85_925CE73B_8F155098
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h5EB503E8_E4071315
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h548BB3CA_4D68806B_6F35D30E_5BCC0749,
    256'h103B8571_4F8A64EB_07461441_B8F8A99C_43EAC7A9_2BE27769_FF7909CD_A59FF10B
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h025EC695_47062345_C400F5EF_1B06A119
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h650A85C3_0237536D_C3E35040_DE9AC1A6
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hF2B35C99_FB71E1AA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h158DED08_E4F2A76F_9E978333_2A8B907D,
    256'h4BE2D5D6_4B257592_9F0EA1EC_7374E550_DA06C9B1_6E3FFD1A_445C100A_FC8083EA
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hCA69B8BB_7DAE3157
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hB7279A2B_D0F45178_ADD4099B_463A9BFA
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hDEB0A249
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h1FB7401D_1FD454C2_CCCBAE2F_94C2CE13_7A1911FC
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h57A6A15F_AA577395_193CDE4A_6705BD11
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h203330A9_27A8CE1A
  };

endpackage : top_earlgrey_rnd_cnst_pkg
