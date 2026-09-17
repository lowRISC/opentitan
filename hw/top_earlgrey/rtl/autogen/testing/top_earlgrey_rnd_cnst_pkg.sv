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
    40'h1F_8E09D92D
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h4431_C56669DF_09018424_E8634CB8_9C35B760_6815CC60_89555942_9291E00F
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h53001011_7F58C9E9_946C1118_0407FEB4_710F404E_6E4FACE5_9B972D1F_DCAF711C
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
    128'h0569397B_FC41976A_C86B02BF_2B89BE21
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h8ECED885_9F464D1D_910540EE_C6BA0486
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hF07CFFAF_7B8B9213_BD8DC7B9_27797C09
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hDFEAF127_2B92ABC4_09056CFA_513AED0D
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hE2186C2B_2A4874E4_ADACA4C6_809E571B
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h351756BF_8D18E24B_E7E1C967_37B726A4_C6F04993_B3E6AAE7_0F22AAF7_48B57C32,
    256'h0264E157_E2C74A28_033261EE_6CEC1007_5C55A820_F842D43E_E1AB1B3D_78F992D2,
    256'h23469898_EB2AFE18_DE121F1E_164EAC29_042563AE_4733313A_D2696788_A8735B27,
    256'h982F5007_A24A125F_876C9CA6_DDEB52AC_92F5600D_2A41BC46_5EFE57AA_3B59BD6B
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h0A402163
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hCDBEEA7B_B1C73698_08D553C8_5B9DAB94_F430050C
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h5E456F3B_26D15F55_84BB9879_BD249785
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h2C23D0FA_289C3348_CE364ED5_34970E1F
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hD45EC606_BE134FC0
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hB716FD89_5F8EBA6C_21018C91_EE7936A6,
    256'h8FCBD735_D35A5487_ADF70DE7_8414D1A1_493FAA83_20476304_C799DC2F_2C2AF1A0
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'hEEE27CFA_19EA576C_A8A8225C_8E17053E
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h44B68DD7_822A6859_F2CF52A5_5FD181B0
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h82D03C58_3756F11A_A5B37F95_44C4AA90_EB97E1C0_F8086F62_7A281C56_81D65666,
    256'h41EECCCC_88876AD1_13C50AD1_BE4D94DC_E8FCA541_28A3860A_E1D3493F_BEF6B9BA
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h5DFE4463_A4615EF4
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h4041E76E_2E74BC2A_21F8A3B5_8E43C0B7,
    256'hF45CC73A_C1C8BF57_20CED44F_6DDE0D5B_38812E8D_B9D146F2_625A7D6C_2A969619
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hB4BA169A_6CD82FAD
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hA8006D98_6B0AFF3A_C5BD23E2_9FDF9C83,
    256'h764CD8B9_57754584_8480E3D1_E6B51F83_71255F32_E98EDB3B_97D392E0_90C29A11
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hDDEA700A_C773FA8D_404E7696_64E2092E,
    256'h0522B525_66D3F311_3CA62FAA_55C49061_7B6CDE03_42EAC7C7_AF630797_3C7F6872
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hFCEDCF28,
    256'h32A66CEA_CF8ED4D5_B616177D_D43B56FA_754E1F53_AD658193_B563D9BD_C6D2AEE8
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h6B5E1B0F_8836111D_5F9C4362_12605D66_704A4F8E_7F864228_94211046_352C3B15,
    256'h31335A2A_4E7D0382_24983027_04642906_47417750_3D442E37_80618C59_1C17237C,
    256'h7E056758_3F890E40_8F97001E_53073E78_9D019E9F_0C3C0A99_95020913_924D5668,
    256'h3990169B_8B49385B_0B6A187B_691F932F_45088332_0D2D4C63_7219878D_26655554,
    256'h85577A1A_76229625_8481752B_915C748A_20796E9A_6D344B14_6C516F3A_71735248
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h0FFAFF97,
    256'h60F5E838_BD8E2413_AB956B10_6CA7139A_07EFFEE4_57DEE82B_6E06663C_291739FF
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h3E00A016_9FB23070,
    256'h79798431_C1B24C98_5D555E31_4AE1F294_ACB2C7B7_8000189A_F02EECC1_017C6EDC,
    256'hA14A793A_BC1F5D7B_9D4A8D9A_A434B233_2FE9904D_4B15464D_A10D9FEB_96F061DA,
    256'h607D9023_1CE27A13_5B6A8260_DA8F0454_FE500C16_CC013755_98C34B03_29A91497,
    256'h11ADA700_4D0A1191_94D0D13F_47047499_6CD7C0F8_11606868_82185351_420C2B2B,
    256'h98560147_48C8E6B8_435983D8_D06F945E_88CD3573_552B8CD4_4B9885A6_CE1A0533,
    256'hE4B91519_B200A096_A77251BF_6242F1D9_F9C78D6A_52402CD7_B96DE93A_0ED5E1B2,
    256'hC16AB2DC_89B11ED8_32AA762D_2A58FC4B_5FC1C9EA_5BB0B041_3CBE1C66_3438C384,
    256'h8A112095_890B3052_1B4C775A_8E3604A1_DE65C5EB_56F1439F_9AB8A19D_B06EE212,
    256'hD46C4792_15EE8A49_AC74C3BF_05FA0CD9_B55013B2_1A920E58_AAD93FAE_80D1955C,
    256'h09B5E9EB_724F6A27_0AB60197_C23FBFF0_6825EF06_A9BC3DD3_48440339_3639D162,
    256'h8B0C9A2A_DB7D1757_90B7051B_A42391D6_0F8E84F6_62F5A4C9_64CE6A91_88756C03,
    256'h402C7A76_A1AC5C5B_90372A81_B47CDF11_D5D97107_768E3A29_40AE815C_5AD30071,
    256'hA8712AA7_2FD3C235_585AC815_725BE998_C13D039F_54695832_672B28F5_15D8E788,
    256'hE2391298_29C709A5_872D659F_124A04E9_A4AC99E2_695CE600_81FF3AE8_F12E14C3,
    256'h6FAA9E2C_07138C52_5D2FC8D0_FD150C68_C0B2DA0E_9C879A32_8F429569_509BD035,
    256'h54885657_7B16FB79_54F8E1F4_ADD1C649_7E582736_D4B8A946_E5085808_57F670AB,
    256'h0B5BE510_B41FDDF8_46981862_B4C41489_0C0A2D08_7F5C3693_132F66C5_D99F8594,
    256'hE5909794_97D0A148_09DB0C61_A390C3B1_F05A499E_480E0420_93B38002_964C4B9A,
    256'h5F666CD1_809C3DDA_76526E0B_835532B0_5D4EE3E9_06C26CF1_70F34BC4_4246AC8B,
    256'h859B89EC_744B0194_517021B8_8463BDD6_8AFE2F74_8D02F104_6B663026_006D2D74,
    256'hE701399C_C176F17C_EB29524D_77249524_562ED096_1AF91E96_BA8886A2_09D7E951,
    256'h248EAA91_3A035D9B_86454CAB_8B0A1780_96AC5493_154CFBA8_CAB58256_28B5822E,
    256'hD60EEF6D_D849E841_979D0356_42AA4DE5_7D9AA08C_501C8A06_23EAF8BE_BD83C2B5,
    256'hDE374A80_486B9296_298A57AC_D45441A5_286971F9_BD7C53E2_56802EA5_305AE0B6,
    256'hD9E6A196_865BA08E_959F5F8A_B8C19D6E_B9C60E47_86A03E55_71266089_97A1D308,
    256'h8C9F8881_DAF4F219_153775A0_3D0C61E1_8F28E064_31A919AC_09050260_AC3C4A76,
    256'h02227A9B_0889AF23_862D7DCC_83360D9E_67BB78DB_4610EA68_0648873C_0ABBB41F,
    256'hB750FBC7_C81A824B_3C5B9414_B119E076_2EDD896A_F178C278_C3335DB8_82C71A79,
    256'h419D0495_D0AF0AA6_D8DD67A8_DDB5C5F6_B180C849_F21A4421_6CB6AD0A_9BA5E1C4,
    256'h2B968874_8792791E_D1138D38_EC8F3BE6_70112887_4509ACA4_132F4BCD_E7A34FF0,
    256'h90CBC654_B93DCA44_54673E7F_43D12572_0144DC20_C9BB910D_C22DB685_56364439
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h7B316D6C,
    256'h12EA8198_70D451DC_29EE296D_A1850BE6_BED073F6_EE870F58_B89FABFE_08C82783,
    256'h7C7867EE_C58FF573_DB5AAF6E_95644DFA_D4262A7A_DB7F05D9_63E4282A_E9DDB8FB,
    256'hE7A138D9_56AC3363_41A536F7_0C3EE90C_AEAE11CB_84B65FDC_5C702578_F9F893C2
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h3D3AC5D2_4E50A9A5_23D8B8B3_4B771B26,
    256'h01169580_DF391757_B3A18805_EB70026B_FCC8DD61_9F133DF8_7FEEA29E_15ED9282
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h1E398FA7,
    256'h1326E771_56C7F9F6_8F102298_AB6A1D31_ED166A85_EA4FD12C_45B2868F_68727E0E
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h0FD2_039DB25B_0760E386_21F80179_1369909F_07C693DE,
    256'hB64CA7D2_EAA1C325_222AC643_AD5DC8C4_89F9766B_8445DD66_D9C88704_FC6D3317,
    256'h24378196_3A0D884F_C262F7FC_B102C733_9FED2FB8_25DDA132_70A8C10D_4B301161,
    256'h0FB9D187_4B4A53C4_E49ABB57_0121B59D_790567AB_D2649358_54462805_8CC25E60,
    256'h31D8994C_789088DC_B6050C1D_C76D2D27_46E34252_6C7AE2C0_91106986_46017054,
    256'h951BE34D_73633E44_B766AD87_C5D34516_610EA041_57E660CC_6C152503_590EA9F6,
    256'h1CEEB33E_9B9C1402_C0C3BC0E_6A550595_8DE459C4_B8E9B13B_65B4C102_208F1248,
    256'h07D4AF98_C2A4A356_9C5D1D45_56E3D418_4E46A712_C74A11E9_94B227DE_AF25EBDA,
    256'h00028911_10551447_01827A3C_240A65E3_256B745A_AE45310F_A0FBE4D0_F6248304,
    256'hA2C467B3_38A74D7F_325AB368_F0C0E77F_49390576_84B82D1C_953480AA_30D420DA,
    256'hB13A8105_EFA6E919_DDA32E60_A15F5472_6B2DAD5F_73506D43_818AC454_DBBC18DE,
    256'h4941ACA5_BE15B096_13C93858_CC8B2812_87A4E284_79583552_28405481_14CD0C96,
    256'h61B95B2C_75053DB8_3B1F9E5F_A62EC172_19E8276C_17EE1655_5E11D010_612BC72C,
    256'h524D3A19_2081D50E_D715D576_0014934C_EB4522BA_FADEA23C_AF6EA599_5DAD8153
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hC2E53370_8CF2C04D_ABCB1602_E203A6AE_6F05F88F_54F52C2F_6B931F1C_D0B35A7D,
    256'hAAA17EE4_E96C9CC9_0CDF87F0_B87B914B_C1D62EF4_3965957C_A510F348_FBFC126E,
    256'h2D6929BA_35A4A240_4E41F964_B7D8A384_668D8236_FF831D6D_0D4C941A_017762FD,
    256'hB1900024_5D09ED49_D5E37217_37AD1132_E0C4313F_A7CD8B57_E69F8508_4F0AEF2B,
    256'h0652B25F_8AA09D23_BB741E19_88D913DA_BEBCCC76_0B2173DE_5EDD464A_DB6875B5,
    256'hBDEBD163_5B5CAC9E_BFC667F6_F138C8B9_28AF7971_890E7A80_C53C3B47_6A9634CE,
    256'h510F60C3_9AC78ECF_0714271B_59614442_15DCFA2A_7FF7EED2_9BCA9256_3EA9263D,
    256'hE1180486_45E8B6B4_22983081_97D45058_B0D73AE7_2025EC43_FED3EA55_9953A878
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h0968_EA219940_6B18626B_119DC45C_4A4BADE4_A14C0376,
    256'h76411D0D_4196E848_D1C24EBA_1A59EA83_0039BE7D_13B9DA12_82D86E05_7D049743,
    256'hE1A568FD_8F6B7B3F_23804690_CA600742_D420AEF6_5516BB16_4E95D5E2_A3C5586C,
    256'h9E080901_B847C388_2F191886_1736F031_91D88D1D_80E86125_FD7D6AD7_994886E5,
    256'h021360F8_75B14685_96DA13BA_5F182619_5BCE622D_78DF6724_479EF073_B5601643,
    256'h48022E05_9871EE8F_03491251_57F802C9_9B2A74BD_1363888A_6A57645D_884AB83B,
    256'hF23DD684_16CA4EEA_7609FA6E_F2419CEA_8BDB338C_4C95C114_D8A02395_4D847A6C,
    256'h845603C8_2006E420_5B54A1F2_E85CD6D4_8C38198B_816388BD_225A050E_4DAFE93C,
    256'h800A6AA7_B961AD51_1D6CE910_36251A70_A80D2850_29A49608_155863EA_984D2339,
    256'h2D0005A2_89D48128_A7C4559A_5BEC5693_C0BF57CA_191B1A70_4B744CD5_73C535E2,
    256'h5B76B0D0_6CA98A89_7D0C629F_9E6C71B5_18C1861E_68D3AB46_34E13EF6_A444AA56,
    256'h647B9AEA_D2AE0E2F_0FEF38AC_E5974676_8F67A876_45E60CB8_9F22D80A_54CB1104,
    256'hA0934D0A_815702A8_1E252F57_0A575A6C_B1A8F022_42224677_8AB1F21D_ABB6A625,
    256'h6BBA007C_FF648669_0DB8A4E9_EB17BE37_2D86B675_82428E09_D12F5363_41BA491F
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hB63F2877_9E797D82_8390E5E4_A8356F89
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h8BA05439_9F71AA42
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h2D9E391E_965D86D2
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hBD62530F_948490CF_A19F5971_8AA34F55,
    256'h09A0536F_E8F5763B_2118E973_86ED75FB_05D302AE_081DCE78_7CC603CE_B266B68B
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h96D48BE5_B6C30F1A_849A1A4A_6E405DF4_DE05FE8E
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hE6A176F8_69052458_0F711F01_7190E3ED_05C573C9_AA17B2BA_F8C063E8_EB49C269
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h574C9DB5_81DC4F66_C2C27FFC_2B8538F5_39BFF9A9_50AA7944_B18FB6B7_6A1F5B19
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h08205A32_959FDFB3_0BE24EBC_A241CED0_AF4217E0_1A53F2BE_7FCBE757_80DADEC2
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hB1FA0110_731127A1_203A94FA_13D41E24_35278BB8_C68210D7_3CDB0FB6_651C2B1A
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h6B5BF1F8_3C73FB08_E172A7C8_5EE09EEF_847866FE_33518FFB_B881946D_B7319EC4
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h0FB2D8DE_353CF8AD_74C66D60_D2F5F466_E8ED1AFB_0E2242C0_5CE59E25_589D988F
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'h6A009A41_C3ADA4B6_638D11C5_22F5567A_C7CF280B_9CD698B6_9BA2DDE5_44D44B57
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hB9F70DC7_1CEBE056_83E27594_5DD3DB22_3C4CE721_7B90B94E_354E9BA1_F613995E
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h87DB8DD9_443DBC2F_A7345F78_4B982902,
    256'hE3D24053_88C4BDF5_EBF9AFF6_D30A8FCD_52677DF9_D787CF38_07946824_D2F97B69
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h00CAB42D_E4AADB22_48723232_922A7B25,
    256'hAB26360F_6052DAF7_EFE37406_1FBBE322_C363CF8F_00F75638_6D2B4AC4_F7F372A7
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h58430B4C_AC616998_706F55AC_8E64E9F7
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h73AC82C0_02B16ED7_7BD24BB0_43FFB8CB
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hAD0B4FE5_9A4156DB
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h4878F654_2D10D79E_8F2CAE33_53BF7EB9,
    256'hCC59461A_4888131B_243624DE_5C3C4DDF_E75DFAEA_9AF6AD7B_21465803_6C384A20
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h11C4AE13_3235825A_401BFA01_6CC4A93F
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'hB1EE33C0_32DB4F6D_29F259D4_CDC771B0
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hD1443241_DA610711
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hCFD53F13_40CF2E48_888764E9_072558D5,
    256'hC263E77B_D216C951_5993BA5E_8438BA01_FCB5FACA_0269FE6C_27AAEC6C_0C37169D
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h96FE3CF5_7804EDB4
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h1D6BD5FF_F4193F7E_9E165958_13A32883
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h4B115639
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h58CE833E_5BFF6209_B21A112B_9B17CD4B_838E2AF4
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h17534BDC_BC618A44_DD79860B_FFDB12E2
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h57B4A856_B1B654E7
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'hDA6DAE07_2969978B_9DFEB84F_DDD8D62B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'hB3F0BE0F_4E808303_769110E8_DDEAB5A4
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h0E64A4B8_DB8D8049
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'hC9418D9C_541A10C7_5C5824B3_9B6BABB0,
    256'h1DE5C4A8_991E9B57_87A8F80E_F80EED17_C9D552EA_D3F23EE7_003C6DEF_58A0F4E4
  };

endpackage : top_earlgrey_rnd_cnst_pkg
