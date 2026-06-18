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
    40'hE6_AEF30D85
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h1589_0B89A346_4430848E_74A53E62_1E55F016_70984751_72903016_4E6D381D
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hCE49E360_CFB594AC_DDF17068_4F6EAD2B_7FEBFE89_5523D7BC_4846A485_956C7F90
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
    128'h4B9EDED0_9B89A754_33566F49_63D9DC27
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hF3ECB11C_E3B87AAA_7ABC8592_0B188108
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h3AFF7BDE_18EACFF8_5679453D_A77D92A1
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h76B87118_AF11CDBE_78D67060_615A20B9
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hC0740F07_969CCD2D_10A1A6E7_988FA528
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hAC032E0A_6138CB83_16FF95C6_5CD7A1A7_68B06E01_06D60EDA_0F1BC67A_DF85BD9A,
    256'h56EA088D_33FFAA6A_1155AFB0_169AB2DE_3973D027_EE30B8F9_01F644EC_7CD3E56C,
    256'h8ED1EC38_739F1D0D_EB7C7741_99CF6DD0_57F44C13_E25C7A58_77BC5242_E6EE63EC,
    256'hDF458AE6_596E87F9_F973DB98_AAA29356_8FD1F31A_0165939D_819D1518_690E6473
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hCDB24793
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h2BA878DB_5CC25B03_2C9B0F81_3A8DFFBA_059EA992
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h661498FD_89197CCA_E8EA08FF_43EFC2BF
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hB1C6AB5C_C63E6F47_41E80F77_7CB7FC05
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h041A1B89_6350C963
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'hBB1EE70F_FDB092F3_3A09C7F7_11D1E2D4,
    256'hD52C4E34_7D633400_1A5838A4_AF883ABC_997A1495_068B7CA9_69B92572_CFD0569B
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hE4D3814F_5116B3E6_F3E331DA_1182DBC2
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h9C894F18_00EDECF7_B17682D2_CE3DB9B1
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h2E1AF433_9E1F4516_4A418EBC_52210D58_DC65508E_869AF565_C1B87D68_7EE837FC,
    256'h119F5BBE_7395CAC3_8919C270_06C23E14_25910840_042A75EC_C25D4E22_67E3BFF2
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h6E003AAC
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h9D582FE8_C9B66147_4BD8890A_3DB79D58_5003A9F7
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h05DBCB55_08CD6CD2_CE715E7C_CEB1BC1C
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h61B3D27B_B8E8398E_880ECD25_2956BA81
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h616362B2_7EAFB903_EC79BDDF_0A4F7DFF_07DB05DE_63910E4E_E4D8A2C7_D4022F16,
    256'hED8A24F8_0EEBCF82_99839C10_3EAE3C2F_18B4666B_5E59D16C_252F9DB7_F094161D
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    32'h818DC161
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    160'h5DC3E1DB_748EB106_3F264F6A_511E6D44_9CAE009F
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hD1534FD3_90C7B068
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h3399BB9D_D51E7F4B_352D624E_1B0553A1,
    256'hCBA34586_AFC766FF_E2BB4466_0290F012_0590DA43_CAA5C708_03FE4A2D_FD865EB3
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h23E2ACE1_4BCF85A6_72995E4C_B764DF0F,
    256'h14B4A167_9D9676D7_111AC9EC_0CF03A4F_DC069806_1778CB37_5ABD1D84_2EF3A882
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h02C22995,
    256'h7B7D1597_40CA72CE_50C55920_BA14E126_DCD0A3F6_C9B71D03_E571BEE0_E47E5B49
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h69646F08_845B0A46_75729E86_784F2C0F_9B2A421F_88564E40_73001163_5537971E,
    256'h067B4A95_0C602E96_27797E39_913B361A_056E205F_8D83166B_8B265749_661C2113,
    256'h74717034_7F508F24_2F044D67_5E4C0365_8117486D_94294145_3C47443F_0968765D,
    256'h62338A9C_079D3290_6A850218_31510D2B_80925C0B_8E1D6159_54190158_2887827A,
    256'h1B359F23_2512932D_10155A22_997C306C_3A988C14_533E434B_89387D77_529A3D0E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h073D9519,
    256'h792FAECD_F66777FE_ED150DA5_FC2ECF4C_99C2FE24_9B87724C_02DEB638_2D21F3CD
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h96A958A6_F6412648,
    256'h64C167D7_535EAB1E_8F78A861_B9ADD24F_02109620_2CE24218_F7A1B233_D5234221,
    256'h3A316B79_0EAB1E02_4538A84C_3B8F1731_AFB3A616_B2F15720_EF5FA5B0_750F0DC0,
    256'h488E8D7A_CE79E005_7C689A6F_1B03E747_1A9D8291_A4D4B54A_E316420E_195702F0,
    256'h637903B7_15FB625D_D6C40035_89F0BD19_8CD85BC4_AF286A78_1CF5BB57_6925C772,
    256'hD3EA0EF3_95525592_D5ADA282_3239806B_90FD97BE_87241967_75C87562_6272A5E4,
    256'hC51E536C_9315B889_ACA4F097_2E50AA50_E60CAD32_42B74EAD_F40A2FAD_5F29BDCD,
    256'h8EA909F9_2E106F84_DA7A066E_569ADC51_60B2AD10_05CCA0C2_D6B5CFF6_56041796,
    256'h1150F65B_ACC8DDFC_69D5B7D7_06761F49_C11F1762_E264A0A3_E0D55A2D_731DA796,
    256'h00B9E273_C1847E8E_A4CEFEBA_D83ACCDA_3B91528C_84A664E1_E61FB3A4_C2C566A8,
    256'h89553806_B0E7C0AA_A08145B2_E93D6BE0_310E354A_9EA64F10_0F646039_F6149659,
    256'h1E59AF07_D9147554_E8E160A4_1C057121_F9A72D45_BCDC0DA5_2B486832_48EC242E,
    256'h509C1621_8C7DEC06_A99B8560_99AE7B96_2D130035_A9446380_1C6B0E49_4D8BB6DB,
    256'h52E2D969_44CC1100_A4853B69_23650C89_8C330A2F_09A95016_9685E862_2F9161A8,
    256'h34868946_5955116C_7A59C248_61877D2F_76D143CA_5F258D85_507438CA_56192732,
    256'hCA7271B7_8702C95A_85140252_A9186FC2_B5E13277_88F8FA3F_2DAA6346_C288AA83,
    256'h1EC4A5DA_007E737B_EB43E86D_07959629_1BA450D8_3D826763_C1CF0013_C8B1B826,
    256'hA8D9C205_30C73057_9AFCA06D_01C611A9_1F874B0C_1BC4EAF5_EC73816B_BC762617,
    256'h79C94B93_E1B3642D_5A52D128_20198608_4CFCB3CF_37846B93_46404C55_2CE40982,
    256'h1457D574_1667A29F_F2A2FD69_1CF5D0EB_BC92C12C_D32CB0DA_231A2F71_9220BB5C,
    256'hEC8249C3_43051819_D14A6F99_E6C1BFD1_1664832B_2718930B_6F5137F8_DD3C57FB,
    256'h35A18228_B05236A6_0677CE2C_AFDC9C05_634827D3_FA25A301_1A7C5F3E_E877501A,
    256'hBA823831_3F0E0D28_C8CD28B0_E8497D26_DBC5E713_1349E4EC_ECC2141A_B8F95B47,
    256'hB9718DB8_829C495E_5EE66B15_4A874495_029A678C_44718EA0_059B808D_92DE31B1,
    256'h71A12D86_1C0C4A00_99B1220F_126268DE_8D15A351_5CBA5D32_A5B0512B_EA7B1F7C,
    256'h09D921EE_04AF4913_078ECAE0_2A5D3941_59FCB49B_9B9405C4_04044945_FD1014CA,
    256'hC48053EE_89B51242_56A51E76_AA4F82DC_271F87F6_A0565764_25B1A9BD_E54091A3,
    256'h6ED244E7_14B85D6B_908A06E6_12FC076B_9AD22422_C0E3D7A5_DC0C537B_B03E33AF,
    256'h52B50738_71E6CC03_C6293AC2_BA475800_09D98AC0_1788A6AB_6432180D_06257085,
    256'hE7BBB0F9_A1469A57_21E2BB85_D17ACAAA_1F143214_3A3F5A23_305C64A0_264581C7,
    256'h408841BA_A0B11A1A_C640D986_68829DD7_C5AE308E_1AB6F8D5_7543911C_DF52560A,
    256'hBD346D25_0928F499_5512C1ED_878693B5_0B700DB1_DDD0C294_8AE22030_9B690675
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h38CD7D7E,
    256'h3B1ABFB7_978189A2_1AE856F1_D908E3F7_0DE343D2_226E9E86_4465A8EE_55EC0E6A,
    256'h296789DE_D5C0AF59_EE62F1FD_1BBEBEAC_2205B1FA_5E94E72E_B7EB1A71_3AD15D25,
    256'h65D9AB4F_BCD2E17C_406F48D1_401F8A6A_52286F69_54C27A9A_EFBE0BC9_EE440C51
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h2295C23B_95627BF7_1A7F4AE7_66DC20CF,
    256'hB404B3D1_68E94491_3FC2EF24_36EED9D8_D834C2B8_046DF1D6_4856A879_6603EC93
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h7E743CE4,
    256'h60442C10_686E8261_3DE0806D_DE1D35AD_6160EE7E_F48222DA_D72D4D62_89EDD5F0
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hC66C0F26_5507B3C1_AA08FD66_BD6DC33E_484B7200_6046CF10_889BD05C_7983DEF4,
    256'h0C2D593C_C81C9313_0586AED9_9250B798_8457D51F_1DEC9FCE_BB1A0B81_3F2025BC,
    256'h6A976B16_9C282C19_14563BA6_F17818AF_F9E8B8FB_F61BA734_22DB23CD_5E35308C,
    256'h89452BD8_3D7DB175_A836C996_4ADDE140_D3F2FCE4_7B6F6743_A08F9AB5_7AFF4F94,
    256'hF3877344_4717B2EA_7C0A7449_EF4D6E12_77623191_5352DA8A_E6CC4261_6829A39D,
    256'h951EEE71_38ED2106_BA02F704_C227F87E_B0E58B7F_54B4D68E_C0DFBF63_CB4E5FC5,
    256'h3A6576A5_0E038D37_9E4C82FE_5B4185E3_80995AAC_70C424B9_BE69152F_A133512A,
    256'h2EEBD2D1_AB0DE0A4_F5E2D7AD_64E7E9C7_CA115D39_F032B6A9_FAA29058_09D4DC01
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hB2D1DC64_55D87F13_C9A46714_46BEA856
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hD5FBB54B_B5B253A7
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h0BC372CF_C9BB0AB3
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hB4E4F075_291F01C5_77A831D6_10543E9F,
    256'hFBB8CEB4_725082DB_3ECF1994_C83D9A81_828C1298_C5EEF584_D6A9E89D_39BF65E2
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h0CF92FE8_B5A20F85_3163F75B_B4BAC283_CD106497
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hCEB3F354_CA2E0893_02C3EE1D_695AA616_283205DB_05CD6C18_888AD01F_E046EAFD
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h8BF298DB_7D5FE0FD_32A29689_A0C1549C_28C210C0_1FF7E6E6_D20E0404_E7B51D02
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h0AA3695D_F42597CA_CAEA4E16_EF75A482_3EE1BF10_0B50C3A2_C1BA79A6_0BD0D947
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hC26D8D3C_3874C6B8_E34A8592_5CE73B8F_1550985E_B503E8E4_0713152D_132E9E94
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hDA720A71_2D7D6B73_26F3102B_A57AB12F_0C11E464_E613088D_6DF2CC43_52AA62DF
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h6B07199E_A6C6782A_D9BB2E78_FA04C689_91DE3B57_A9B61206_E6C0A2AF_A6A3C56D
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h97128C78_11E36A28_29DB025E_C6954706_2345C400_F5EF1B06_A119650A_85C30237
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h536DC3E3_5040DE9A_C1A6F2B3_5C99FB71_E1AAAB3C_208383AD_F50311FF_71FD4692
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h1923A8CD_8C6FF98F_9BDFC2B2_05D8690D_D35500E5_A51BBA34_A71D81E9_EB876B6F
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h1996B2BE_4B58DFCF_B830B9E2_5BDAA3E1_AFFA9180_6D01A89B_DF5084C3_F043FE74
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hB4FF850B_4A6DEA97_774B63EF_1E13CA69_B8BB7DAE_3157B727_9A2BD0F4_5178ADD4
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h099B463A_9BFADEB0_A249E67A_25FEEA95,
    256'hE50B27DE_DC6815C3_75B4BD85_E84AEB69_C3F4DB75_1585B16E_D45D55A6_C1FFD5C9
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h2099CDEE_A949DC96_8AC70991_C5514057,
    256'hA6A15FAA_57739519_3CDE4A67_05BD1120_3330A927_A8CE1AC8_8224A441_C4192ABE
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h1DC426FE_EE2C9B1C_8B34B1A8_21AFE522
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hE11C4049_D9B85F9D_C3C99A37_868579B4
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h6A84095E_A981140F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h5A967415_A06C4FE5_E0CB7BD0_3E354789,
    256'h131E2822_308439B9_EEAFEDB8_B7C6380D_A7CC4928_51BE18E8_D49D265D_5CAF1F3D
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h8B76B9B8_EC2F4F0E
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hAE6D9D26_C47E2790_80DD58BC_F5AA54A3
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hF54824B5
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h33AEC0C0_5C90D197_FB474FF7_45D81329_1B5EC558
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hAEFE46B7_A5195322_D57D74AF_0790F505
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h0E1343B1_8DDA6827
  };

endpackage : top_earlgrey_rnd_cnst_pkg
