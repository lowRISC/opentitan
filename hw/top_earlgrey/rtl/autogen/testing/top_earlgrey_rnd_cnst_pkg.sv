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
    40'h60_CFB594AC
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h5832_E700C61E_84704238_48851A34_6495D64F_35241480_95E62157_CA6D369C
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h3AFF7BDE_18EACFF8_5679453D_A77D92A1_76B87118_AF11CDBE_78D67060_615A20B9
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
    128'hC0740F07_969CCD2D_10A1A6E7_988FA528
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hAC032E0A_6138CB83_16FF95C6_5CD7A1A7
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h68B06E01_06D60EDA_0F1BC67A_DF85BD9A
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h56EA088D_33FFAA6A_1155AFB0_169AB2DE
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h3973D027_EE30B8F9_01F644EC_7CD3E56C
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h8ED1EC38_739F1D0D_EB7C7741_99CF6DD0_57F44C13_E25C7A58_77BC5242_E6EE63EC,
    256'hDF458AE6_596E87F9_F973DB98_AAA29356_8FD1F31A_0165939D_819D1518_690E6473,
    256'hCDB24793_91635057_CA1045B9_E1917E1F_F0189B04_A4F7FBA9_60FE098A_4FB9D469,
    256'h171B950E_364B0DAC_5469568E_661498FD_89197CCA_E8EA08FF_43EFC2BF_B1C6AB5C
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hC63E6F47
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h9937CC18_FF4AE451_6A1EAB68_A646E3C8_2CF707A8
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h84DED1CC_79BD6787_D6663AA5_E622682A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h6525E083_CCDDBD2A_1B008057_C22C884E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hD49D87A5_B56BA735
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hD7BC8D70_A4A39A4C_D52D1FE5_0B9A210E,
    256'h77971F76_AFD167EB_006A6CB8_4305F938_1D89BABC_3BA636C0_9B71F786_4140850F
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h65C1B87D_687EE837_FC119F5B_BE7395CA
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hC38919C2_7006C23E_14259108_40042A75
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'hECC25D4E_2267E3BF_F26E003A_ACBF7D51_3AEA01E9_EE420D5B_523F6B00_C81BDED7,
    256'h282425B1_BB59B801_481ED579_3ACCFB3A_F884AE37_8405DBCB_5508CD6C_D2CE715E
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h7CCEB1BC_1C61B3D2
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h23658DB5_77216F7E_353FC486_33B1541E,
    256'h895AF506_6611176A_2EFA7993_09C1D130_BF02B7EC_C72620F9_5289CC38_A33BAB9E
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hE05775DA_90406D9C
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h1C53A3B5_9349DCC2_ACC569AA_210DBB0A,
    256'h21BF7A75_7AF81C35_F7286F4D_445B7EB5_C3720D1A_7584A590_0A2EA7C2_C43F9E33
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hEF16483D_DD53E775_9B85746D_11C6857A,
    256'h44813AC0_38833A3C_ABD3761E_FCA20A58_D4A55AD8_7CAEBFB8_698CD09F_A7C0B403
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hF7C06C69,
    256'h10E727CB_ED4EE2B1_9EB8B9EC_47A05221_A8D0F96E_FBEEF3F9_FF6B5876_7302C229
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h838B054A_0F34376E_9A65792F_69873936_10066F8F_9C240C4F_8E751F5E_6774251E,
    256'h2E969076_3B46045A_21134289_222C6223_66008157_8C566386_8A48602A_64945D27,
    256'h92983517_2941453C_6B443F73_844E336D_68328255_99021831_51912B1B_885C0B80,
    256'h93619B7F_19017028_9E8D0D78_1A077C4D_586A1209_5F7A164C_47080A2D_111C8554,
    256'h306C3A9F_533E434B_389D7752_3D0E495B_7E71031D_26142059_50724097_157D7B95
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h108133B3,
    256'h8A7167F8_2D4B5453_CA029357_90001030_32EED900_BB073D95_19792FAE_CDF66777
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h19F06B0C_30BE28F8,
    256'h08896F4A_754F1B5E_90991573_76C74AF0_7B9DEDD3_627213C9_D1DDAD9E_86686578,
    256'h52DC8350_DE7FCF36_51851C46_F89D0530_C219E0DA_39EF212D_E07DC7E9_8719C3E7,
    256'h04D6F49F_5F06D983_5C63F90D_0A77CFAA_1D46B26E_29262896_8F13D8D3_43634910,
    256'h6B66C400_C6A5BD5B_3155C393_9116D03C_2850FAB1_6C329319_D0D03357_C90ABB3F,
    256'h94526025_532D6C51_826DC178_57158E8D_27B80547_E90B65AA_B9A6317C_5CBB8F70,
    256'h726C00C8_47A62D6A_2603B816_A5806B3A_84C41658_F514BF62_14B1DDBB_E7625190,
    256'hA46E9C79_CC6FCF4B_6D8C7923_13568B62_12EAD630_4F69553F_16549962_6A484402,
    256'h9846AA80_2047A0BC_AAD79470_3FA7AD37_60D76F1F_93BE2931_893B8072_B31E1860,
    256'h8BC39CEA_19D5BC2C_827C01BE_DDA2DAB2_702BABAA_05111EB9_B53C7181_B41C6EBC,
    256'h5B875A56_482BE79D_0C9D65D4_9C85476A_EA7C4719_22403917_14ADA619_CFC125B8,
    256'h68D68F8C_15AE6572_820ADA55_A08F27C9_02375555_0172ABD5_B32DFD28_DDC8F30D,
    256'hC70CE8CE_7FA4CE20_51BE01ED_F00A1F1A_0043C009_8282F396_D53A2B84_960F7C69,
    256'h87F24C2D_1572BA5F_5FC96A02_1C544562_E17DBA24_B36E9B0A_2085BCE6_80683B10,
    256'hEA74F028_D9D209A0_EA356804_56051307_265F4C45_127E3187_06AD6771_350EF7C7,
    256'h522B18DF_035C9B3D_7502CE33_E08C2364_1A98AA94_4E9948ED_1F64D2DC_42B16A45,
    256'h26EB78C4_347A128D_53B5383A_64A66708_DC6B8FD4_98136029_D5693483_02DC5C80,
    256'h1696A576_D87B1620_31188817_05784119_6716A6CA_4FEECC00_D106104B_79012446,
    256'hD5DD9A0C_937B1D84_9FB0A30A_FC5D2136_9AA251EF_3A689B78_A8E68AA9_666398A9,
    256'hDE140C47_F98193E5_36252AB4_0352B4B0_B7161897_03678B39_EF085B47_C0B8B97D,
    256'hA17751C4_25E94A25_9163B125_41FA661A_73FCB108_D8799CB2_65E077ED_CB0B19F5,
    256'h3490B5C3_E130C09A_EE129862_1341A5EE_FF365232_3E14C6A8_A918EC45_5B584273,
    256'h88DD97B4_BA59DA30_41086350_09A16699_26AB9EA8_B8EF607A_FE279CD8_89A595CC,
    256'hCBE8A44E_878C3250_2AD1A3D4_FBA80835_581D324A_057D9332_08ABE688_18C5D1B2,
    256'hD42B2C20_DCEB98AB_027027B9_23713A2E_7CEC0054_76A8E162_1A26C170_1419EF69,
    256'h0701FE5C_AFD39B48_1F181B05_8C450015_91AB1F2D_6034A569_509B163D_030A98A4,
    256'h4CA9B464_77980A8E_0A8BB67C_46C49928_CF7152D8_B2992F85_B6E46996_6B30E058,
    256'h42D64961_1962EC15_60246CAB_7064796E_AA1386A7_A4A2F391_4175EB12_BD0E5514,
    256'hA15EB417_8120893E_86DBB185_38824BF7_A8FC82E7_97423252_0484D839_8AD2F0F4,
    256'h2B484815_70A29BC4_67469C68_2403E43B_22254AF5_7E7960D1_64349A51_6A321E29,
    256'h685656CB_1CC361D4_82A05334_A12B7D70_92557631_C532F66E_129AB5BA_B903DACB,
    256'h948E6BD9_C31408B3_4331447A_819248ED_A1979C72_1CE04C21_D24B0B4C_8BBA5C54
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hDD57022C,
    256'h77EDE860_9C409D90_5B3C7819_B26A6743_28819928_C5D79BF1_DB63D11E_1C31BBC9,
    256'hA8C73FC4_CC3D14CA_6BC0B968_12DE7C77_5A54FF19_343CB320_40B34907_68889D27,
    256'hE0BA8588_D34C05BC_F127DAE5_8B65D6A2_51088099_B37107B1_CCCF1A95_5F03DE1A
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h1E660F76_927603F5_BE6758E8_2FB16E04,
    256'hAC3DC504_CD11A21C_0C2B328B_C946AEA7_CE5576CC_934EB77B_9CD2E149_ED82F461
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h3AD15D25,
    256'h65D9AB4F_BCD2E17C_406F48D1_401F8A6A_52286F69_54C27A9A_EFBE0BC9_EE440C51
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h254FE5E8_AF2840F1_7DB2234B_1EF46742_0BF2EDDE_160C97D3_8CC481F0_557383CC,
    256'h5CC27F19_9D20EE3E_CE75D753_7800B336_0E3AA343_9E65A5F9_056C5E79_FAE45FAC,
    256'h881B26EF_9AD17118_49290AAD_175621EB_3414C64E_4ADDD838_1CC7AEB9_94FE54D5,
    256'hC3BA1348_7B63FBCF_453FDA86_1247E78A_76C87250_278BA2A6_6A913B9C_52079B46,
    256'hBEFFCD5B_41A85A70_E36915D9_3351EC2E_0DC06411_5D39BC98_B7F609C9_89624D2D,
    256'hFDABB4B1_AAB51D6D_80D46182_6E68102C_44E93C74_7E35C190_7A03B8D0_32E0EA57,
    256'hD2A18466_BD08BF7C_31FC8722_6BB6DF06_F8E2968F_3D02A4B0_9F2F8EDB_240F6F2B,
    256'hA0D6E1DC_BBA7F577_8D603730_2AF704E6_1A59C593_928558A9_1FF39599_01CBCA4C
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h234377E0_0D28EC32_FA5850E8_A7F607A4
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h9B2CADE1_2AF0DD48
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hB9227A97_8179AA2E
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h442961F7_335BC768_943FFE41_B4449098,
    256'h7915D32E_0900AC03_60BD6A20_CA2C7BB7_2F4C5AC6_5BCFA39E_E67A39F7_60A57DDA
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hDDFF02E2_6061A471_3D036917_1CB834F7_789B6955
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hC96A8130_AB336462_CEE1BF8C_653FDE5A_40A24DF7_8E146916_DC55F8CE_6DBFAAD0
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h8910FBE1_822C22A1_7A376FA1_315C0CB3_C29CF4D1_0AE5C8F0_C7B034BF_23C9068E
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h307D8513_B7734AA7_8CC36F94_7A2737BB_C0ACD144_7BAA83C3_FC818BB3_B4A840AD
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h3214CEB3_F354CA2E_089302C3_EE1D695A_A6162832_05DB05CD_6C18888A_D01FE046
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hEAFD8BF2_98DB7D5F_E0FD32A2_9689A0C1_549C28C2_10C01FF7_E6E6D20E_0404E7B5
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h1D020AA3_695DF425_97CACAEA_4E16EF75_A4823EE1_BF100B50_C3A2C1BA_79A60BD0
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hD947C26D_8D3C3874_C6B8E34A_85925CE7_3B8F1550_985EB503_E8E40713_152D132E
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h9E94DA72_0A712D7D_6B7326F3_102BA57A,
    256'hB12F0C11_E464E613_088D6DF2_CC4352AA_62DF6B07_199EA6C6_782AD9BB_2E78FA04
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hC68991DE_3B57A9B6_1206E6C0_A2AFA6A3,
    256'hC56D9712_8C7811E3_6A2829DB_025EC695_47062345_C400F5EF_1B06A119_650A85C3
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h0237536D_C3E35040_DE9AC1A6_F2B35C99
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hFB71E1AA_AB3C2083_83ADF503_11FF71FD
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h46921923_A8CD8C6F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h0A27172C_4919178B_4F79F468_52AF6F27,
    256'h977F3886_102AB4F5_CFBEA731_64A5C5BF_21807C8D_B86A4057_40DAD81B_30DE68FE
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'hADD4099B_463A9BFA_DEB0A249_E67A25FE
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'hEA95E50B_27DEDC68_15C375B4_BD85E84A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hEB69C3F4_DB751585
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h8C763E28_02D13564_E024E78C_E457F6B6,
    256'h1FC369D9_F8B84BF4_059DCF1B_172BF28E_BB414902_8A54AACE_6232F70A_555F56EC
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h9DC3C99A_37868579
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hB46A8409_5EA98114_0FF7F0C4_AD73D597
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h26774A37
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h816ABD5D_0E7EFFE0_E6D119C0_99F452C5_14D230DC
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h51C3DA59_67F2CC89_F1B0ECA3_388F277F
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hFAE4319B_4144B76B
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h7C902A9C_89F6F8F8_856D8B76_B9B8EC2F
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'h4F0EAE6D_9D26C47E_279080DD_58BCF5AA
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h54A3F548_24B5C653
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h745EB351_CE170EE6_0C7F91E0_6FD36C20,
    256'h29E5F80F_E43FC130_191495A1_9AB13A14_2FA5E4ED_2B5D325B_60662F72_7B6AB8A3
  };

endpackage : top_earlgrey_rnd_cnst_pkg
