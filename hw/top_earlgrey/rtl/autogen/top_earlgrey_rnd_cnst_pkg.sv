// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h4B_8C27F623
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h0013_C3505287_4217A511_708D64C1_987156E3_80B7E74A_221124E9_9669391D
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h2AACDE59_D762AEDB_956457E6_728EC069_EAF43BCB_B5AAA266_76B5C2CD_D6DF726D
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hEA9EF7A1_1BFF9AD4_06000A55_C04AC1E9
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'hA5DCB742_32F964C0_1BBD5CBE_7ADAD2F2
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h81BC3063_58CE3601_0B02D4A6_68CE7861
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h552D118E_85763D58_287F126A_F1D8CE82_2406BC27_99D4675A_ED04CE47_4E3C6DBA,
    256'hEB4D5B6A_87BC2D99_CE3A1FA0_DD916824_E2065957_DE2B4CA2_06E85CC8_2D3FFDBE,
    256'h3F439926_A78211D6_EC837709_71991DA9_17554361_B7B15655_32DDFA72_CF1ACAE7,
    256'hC82D14B6_02507DE9_568C262B_38B08CA2_69F37FD6_32006CCC_528FC226_E4DECF53
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h5E4634AC
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h30157392_AD453BE1_BCBAF861_84B05674_799DCA6B
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h56323573_6B4FFA30_EBBB5FDF_1030823C
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hDDA02056_992351BF_630A887D_D6518F51
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h7A899374
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hCDE9A1A0_FF033751_17048452_BB49F337_9DD6A83C
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hFF2F153E_8A5FDA0F_D66D0D58_5BABA6DD
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hA4B48268_850C8359_145B0488_80978EFC
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hBD90759F_733BDBA9_B53B2C0C_7227B780_545DBE71_83B8B51F_72254B8C_5939D063,
    256'hB01DDBF1_E703DA21_5D8E6FD1_91FDE7C4_3A239631_1461A6E2_60268A5E_2EE646A4
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h727FF204
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h0EED4181_F315C9AF_4971CAB8_5861CC31_D1FAF52D
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hB46E22AD_8998244A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hEFEE86D5_F426D248_2A3B0FC5_5BCBADB2,
    256'h9238894C_A5C5AF47_4770798D_5098CCD2_C3117649_00A3E1AE_86D27AF7_367539CC
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h169BF2DB_9F1AC1B9_8833D67B_DC7080D3,
    256'hA3AA85C4_6ECCBB2B_D4D63F96_35DDA064_93E14F96_7F13E78A_D5500642_840DE809
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h4A0EF78F_37681AF9_A814FDBB_848CEE0B_C10A5D4E
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h037B1B89_42299096_91189A1C_0E3F9341_592A1349_9B373887_9F3A7586_358B165C,
    256'h8A953207_5E640171_28114D6C_726A524F_2E998C27_8E3C5717_265D466F_5F606D79,
    256'h484E2015_62120F77_7E4C5402_674A9E08_5A338F0B_977D3185_582D9461_9C3D8040,
    256'h980D847C_510C7330_668D4B44_762B2306_9D565055_3E052C7A_631D7414_251F6E45,
    256'h34096821_88696B2F_3B781E00_70828353_5B244322_10476504_1A7F1992_0A398136
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hC7E06A05,
    256'hF44AB76F_C135E8F0_14275406_E989BBCA_2032F005_06A54E89_2A0B11E6_D1A8F7E4,
    256'hCB9394B9_29A799B4_3D0FEE2E_6B799677_D2B4D25B_38BD6FA5_1963D4F5_E95324E1,
    256'h0D6B791B_BC8FC970_032D7E0F_D358FBB5_B80CC6C6_51406786_4EC2ECA3_60350F62
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h4AA9E473_059C2EE3,
    256'hB630A890_69CADFC0_A4304ED3_6504581D_F86EAF70_7227736A_301C2EA2_563BFA14,
    256'h8022A491_FE3B0158_76FC821E_BBCA9857_59D248EA_87C75A01_BD53E053_40CC4DED,
    256'hB216C525_8105C1AF_61216746_DD038239_DCD9AC5D_9020A073_CE9A1CB9_B8303436,
    256'h6F6329D1_6295AA93_5956E77E_A12C5179_531E12AC_FD0B5338_45FB12CC_B1D17610,
    256'hD852D16D_ABE1AA0E_C88AC2F5_567B69E5_EB0D9CB3_6A83819F_1A2B4149_6F5445FB,
    256'h5A24A6B1_CB097331_06DC12AE_74113AF4_363EC999_A9036C4F_54209E90_5D8BC55A,
    256'h5AA8517B_0A4F0AA5_7C4F350D_5BD4FCA7_1504F6D2_689E0110_1E74929A_51969989,
    256'h37730892_9AA28DCB_1B1C7AA4_B82CADE1_3ACC9B4E_3A3E2E12_003AE13F_4B1150F8,
    256'hD394A0F7_78C11064_E2F06A23_8B0598B7_9D536484_3AA6DF45_E92D0DCA_52264D06,
    256'h2DC395CE_C2C022B5_743C1140_1A4979A5_4076AD7A_07D06618_39B15B8E_E91DC7B6,
    256'hB943A902_00C23772_2FDB44A9_6B20946A_A774C7F6_A40A1D8A_E46567B2_50C98887,
    256'h6363DC7A_35520F97_C60C0027_853451C4_43D3D292_9E47A292_8845AA09_099B2105,
    256'hA0A51FA0_5E997083_5157F006_A66FEBE0_E4C80881_F5585DA3_4D214299_538CDB1A,
    256'h90BB4C97_C2EF256E_48E7073F_D1090250_5A5AD339_4736CBD5_11056097_D52F0C47,
    256'hA460686E_61B10C3E_5D9A5207_05E78D1F_C3A1CC69_6EA22293_838BE376_B2880BB9,
    256'h9DC915C7_10992E43_93809D52_8E872B06_5F4ECDA6_4210C36F_FBAF1B69_9B4AD48B,
    256'hB407C489_172319E3_14E44F85_9624986D_EB7276A5_6398B916_659595E7_B6C09825,
    256'h121A71B3_96B8861E_B628C715_F9BC1F78_D83C270B_A5F8DF6E_21C1BC82_C2553584,
    256'h3B4AC669_2DB00D42_8692B94A_27DA39B3_5ECE76FA_2F60C651_93125944_DB5D34C3,
    256'h8626D4B5_5726326E_9F33C63A_2D7C171C_6AC1B623_D4A309D5_AF1EA9E8_F64E42A1,
    256'h2A8A1845_B84D2776_9251F9F6_AFF18686_735E20A9_D891BCEE_1474C35D_DA3B3C0F,
    256'h40904ACD_9A285802_9D011547_06AC1183_4DCC4D40_BD031788_81015607_1229C065,
    256'hB682FA13_27E3E284_65E4C701_75922CB0_91FD0C9E_396A5737_A9130168_56DEC41C,
    256'hCA360AC0_2D425618_1962824C_AF87D562_460162CC_7894C12B_69F2B9A3_1401DD9F,
    256'hD8F628E2_B971F896_44181305_655485C8_070A477B_85382D09_8B63C9A2_1B6E6BAB,
    256'hE4B61189_F2FE6E3E_8E161E23_A848AAD9_0A88A039_B0045C71_A3C6978E_1FF06DD4,
    256'h728C69D1_6C299EF6_EC798999_95B9BCB2_98805C90_52602811_118FDF3B_ED91096B,
    256'hB661263A_F1951A3E_AB09ABA0_7343D232_51D68183_44C572C5_AEC7906B_0B1A80AD,
    256'h0BBD9920_327C034F_23CF06AA_F1D8A054_0FC498B1_95448216_4CC72C71_7855572B,
    256'hEC7B8838_98632050_47992D91_9DDF4E9E_5C00EF0C_EC470CFE_10AD5344_D6B50972,
    256'h89D746E6_B35E4F6C_A9650619_1A5DB3BA_3B8CC409_66863DC0_9804564B_C8D590A8
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h37E9DB01_9946F039_C1DE3D4A_2D2F9224_42ABB52F
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hE6D750D5_7961512B_F4AB8199_80D27044,
    256'h870E7C36_2B927CEC_57BFA913_28FFC7A1_7D59E02E_4CBD8F04_70A66A22_8CDDBA3C
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hD1CBE307_C6E9543A_E4C4F7C3_B0B6E5DA_CE113069_A66FB598_4B4E0CAA_4E4071E1
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h3F1F9588_A0C08A1E_98D87A0D_98F784B5
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h198BFB42_3DB3E366
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h0FCAEAE0_B73A6E1F
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h2A607878_222D1431_AFEB6DCD_A93CE946,
    256'hE63BCAB3_8BE449FF_7406FC6B_E8975944_A8415923_33472125_F1E5C598_2CF4FC35
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hED436D21_F89B89E0_14F04E54_35B62615_F74973EC
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h6BC0E7A0_B5C48538_7A153AF8_38100D4D_7E05C1B5_190F9A24_B1FFAFFF_9B70D638
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h5D284E54_CD7B62A5_8D7CC59E_2D4770F4_8A32B276_C6C7088C_9553A31C_2C04C8AF
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h7C0D700A_B56106A3_40A95E26_6F08902B_111C05D6_C2E4062C_6BA16381_E2B77578
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hC8B5805E_EBF2594F_FA38C060_37AC8241_EF750536_005D24F9_246BEFF1_5BC36F07
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h0AF27CBA_F7F2714B_6E8673FC_EF10B6CA_DC364E58_DD8F5DA4_1C08552C_AE1F1550
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h34FF5BE4_015B5556_CB0208FE_3B3556D6_8DACA4B0_86241917_D9FBC3AC_5511B7F0
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h4B36CA5C_034C4B69_DE2B2958_E7B8F499_6AE46F28_1F899F6C_BE951E34_E6E9BCA3
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h19AD7851_E961480D_702B902A_2D88CC22_366C5178_8C7E5176_A1D50507_F9AC2534
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hA4BB5DE6_87776284_44C5C08B_0EF4ED43_624AA3B1_FA887841_DECB42CE_6678758E
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hAB5270E8_6691C606_A50602A1_94C021B2_C89B5080_C7AE8CB0_02081B32_970BE393
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h95AA5D8D_5F187AF0_24B17E36_0503F8AD_5A497589_8DD474A0_EDD0CCAA_56665D41
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hEFC88ECF_2844F3B8_18AB595D_1591AF58,
    256'hC54CEADD_80DF40BF_F19FA408_24C186FE_60D2B205_55B0324B_FEF0EC32_8717E65C
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hA850D7F6_FB4A4CE8_63E6C08E_6642253E,
    256'hF5020ADE_71B69DFB_2BD505C4_6EF000A3_48082BF9_125C916D_CF7CCED6_94212EAD
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hA837139C_A8CEBC36_2B042A80_C51DFC51
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h9DBFE87A_88125889_3D7E577E_FE0D6B17
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h55B66619
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'hC1C695F8_3DACF6E7_F0A6CB54_CA0817B6_A5047C91
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h8246FA17_650C6870
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h548DB490_F18E2454_E3485613_1979CB06
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h1F7849C6
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hEF86F228_455E26EA_B517B30C_7D87304D_3F28F340
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h1206C59E_009CDF86_F638B7A1_298E6D1D
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h44F6A11E_6593F48D
  };

endpackage : top_earlgrey_rnd_cnst_pkg
