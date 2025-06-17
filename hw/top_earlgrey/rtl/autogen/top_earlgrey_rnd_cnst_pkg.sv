// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h4F_64CE9783
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h30E2_CD723991_58391075_36995C51_1E9E57E0_0A285B28_F0151D42_58206481
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h7468BC0B_D8D70368_E7CFB11A_99675B14_62406193_35A9E2D1_23834D18_744778BE
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h5E63C087_E36838B5_6B1A45F6_FD312F53
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h53FA7B2C_E9FC83DD_AF1DD8C5_A42E2AD2
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h4FA02221_B6FF5AAD_7A9C09D5_D9FDD1CF
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hCF512835_C0CFAE2E_D0C69FA4_88685CEA
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h9BC1C89B_FB7399AE_F5C6EB5D_6E4E2341
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h6A0AA6D7_AC7EC9C3_304470FB_E505F964_9400CA98_64FD4CE4_9D2CFC6E_CC102540,
    256'hEAD87347_00A52071_32689471_AA822BC5_1CDD4D37_AC2D246C_4264F37E_C1982017,
    256'h94ADDA1B_16929DF5_E06A56AA_DED44325_9FFB5736_DD680121_5B98E162_DCC09E31,
    256'hE8382E46_E4FECFDA_2375A614_7421D8CB_69D4F3A1_5FAF834C_AD515D76_BD37C7BE
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hC5F33FDC
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hC65720DC_8F9A845F_6A1C6251_6AB63D39_BE0DB874
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h4B6A0CD0_66336E9B_0BDF6A55_F0D23BB7
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hDC0DC524_D3B05546_03562188_552794DD
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h2BEBF67F_318B5A49
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'hE4E6D896_C3E8066E_D32909F0_49E11DA6,
    256'hBC488997_F75A101A_F179382F_2D7F147B_7A08672F_D2344DCE_026A53E3_2EDBD543
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hF0EF4782_48447B11_42087365_0CBC6AEE
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hA2C8EE2D_E417E3D0_5D145C3A_684922F7
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hDC57CC66_8C58F099_531A3221_A2EDDCA4_1F778DDE_61DE9734_B7ECDEC5_17110ED2,
    256'hCEB31D78_9F996BCD_43BA4FB0_6B9EA47D_BF441AA6_25F5DDF2_DCB03C2B_867024D5
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h4654C6E6
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h50FC8F9F_B826E306_841C34ED_A63A45A5_D79155E9
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hD00B7E75_6F81353C
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h530A34A8_127F92F0_C6D8BB5C_8C7E515B,
    256'hDED97579_5FEA686C_3B5BB317_EC7C4A95_4841B013_DCF8028B_263828D7_A768CAC4
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h8AC7AA1A_9FC8115F_247475A6_FB7C4F2A,
    256'h0ACD7359_6FB7AC97_B9315A27_051BF408_D0042851_6730CBE6_8E1F4B66_0E9FBD0C
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h51A50AC3,
    256'h12C18282_2CF6AD12_452480A6_1092E8A8_0CDF2678_89E06A8A_1AB5F6DB_8158AA7C
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h377A4A72_7E8F3570_24262156_918E494C_104F305D_366B186A_1583878A_758B882D,
    256'h5E0A972F_082B0B84_29400792_763E2290_1F041247_4E468543_71963C41_4D091168,
    256'h02935B1B_58949F0D_146D0155_1E57277B_541C1766_787D8660_732A6748_20796238,
    256'h77336F99_196C312C_3D162E0F_4B513F81_42450E05_9A741D59_7C23069C_699E8C13,
    256'h5F53809B_390C5003_4464653B_3A619D63_7F5A8D89_321A5C6E_95520025_82342898
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hD58DC810,
    256'hDD8EB122_5D79F3EC_320BB4D2_D4692B1F_9D1645F0_37D9DC83_E4B7B7D0_E5638801
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hC75C2A17_1038E805,
    256'h291DA85D_B7ED8E8A_AAF49E5D_2515B5ED_A1A9A3CB_C41852D1_146C5E48_1BB54AF8,
    256'h0463E0CD_78B8B1F8_4C97222D_9533022A_AF44494D_B94418FE_B56C610B_1D15831A,
    256'hAC2D0C3B_EB718934_1E475AC4_5CB7CCE2_CAD3C72C_F378500A_C8C5C2BD_60642B40,
    256'h6E90D559_05750689_21C435AA_97374819_3B86D5FA_111C2B89_0143B590_A19C434E,
    256'h30D68227_3A1F2264_950BE4A7_ACA887E8_F8268351_97F9729F_45A958DC_BFBA5A3A,
    256'h60FE36CD_D8163860_DB8A6454_2B5A505D_CA164651_A1657116_C26C762A_6C3C46EF,
    256'h3AA0F04D_A95595E0_B8639D40_BB35C048_81FAE71B_27250341_843B0F91_AF1E7F0D,
    256'h4AA28DA2_9CE77231_96D860B6_7871C226_4B091802_45459B4F_226BF8B3_AFCDF3F2,
    256'hD29609FA_B84864EE_37515815_EA49BD9C_A6976609_DE6BE640_86761CB1_A6657A3E,
    256'h0A5888B7_C39EFA48_25506F5B_98F40E11_F0D8A49A_87B8B6A9_2108E6CB_0F035F72,
    256'h404B1000_6A3A3D82_C6967A9D_A4049136_3A114931_6C476B64_992E299F_DB5144DA,
    256'hC05352E4_7AACC272_D67A0792_60C9C811_2BB7A9FD_9C26C23D_4579D1CA_8E36AF91,
    256'h81FD397A_64769055_BE831BDE_F259997C_31DA9229_6746B043_E0361C5D_3319FA9D,
    256'h3D63C741_F90B5765_2399B67D_A0E009E2_1B31438A_3570D648_7A0DB1A7_D360660E,
    256'hC982AEB4_1BC61056_ED0DCAF3_E8C855ED_44B5FF7E_8ED0F174_88D599DC_82168128,
    256'h1C20C566_EB82D162_85F78671_31906420_BC5CB059_F9CBC480_FA2D4071_9CD5F273,
    256'hB1536A1E_C186C4C9_7E816327_2656EC67_6252BAAB_86AE744D_CCA70033_CA190EA7,
    256'h94DDD69A_6978A196_AF0B853A_74A80053_9046BA14_FB610979_43D1AA2F_6E971C5C,
    256'hD77B4297_98524B1D_8B7168C0_C4F40C42_1F16928E_5A5DC8A9_AE66BFCF_35690028,
    256'h56028989_5BD3F652_06A11F96_894202B0_42C0B433_6146C27C_542E4C66_086A014A,
    256'h0A8634D2_B2252522_C8627947_98AB2616_67BCDAE6_34FD0FCF_1C59D509_9CF551B9,
    256'h2ED2E4CC_7719123C_62C24922_4932348C_9BF32967_AE823B29_7D01EA22_75C51396,
    256'h20C05381_19A4C42A_4A8C278D_5C939615_AE007659_0A6D0232_DF51F5DF_6224D4A1,
    256'h6AC29044_85F3B266_DA20FB38_294918A6_3551974C_1C8840C3_17067A2D_A646F0BB,
    256'h8E1A2700_436AC6F4_81B78013_DAFC159C_121C9675_C0428129_06EDB984_1D8EC835,
    256'h7D01BAAC_8202F9C4_E7B022C0_80AD79A1_2FAB6C45_4C3497AE_B025BE46_930520BE,
    256'h450D2C22_188B9E03_66E18C16_E950E73D_DEE85AD5_47A91994_DC394FF5_B65662C8,
    256'hDB31440A_0A7128CF_A4C85162_9E791F18_48C385DF_0C1C3E44_2CB94E44_245496F0,
    256'h00A32155_E5AB876C_E699D095_E4F3C1B4_AD839344_EB916608_82553D56_33110730,
    256'h22B7B0BA_8709A2B1_328B0782_C5AC0410_5038D6BD_A39662FB_98D0E726_59A942C8,
    256'h04E945C7_34ED3A82_9F405A51_6DCC76CE_332D8C17_F9A7B76F_D775F84F_980324BD
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h75E7B120,
    256'h9B868A4A_CD919ED9_795D5F51_9AA8CD47_AC68B656_50A1BB5A_4A6DBF0B_C7C1C7AF,
    256'h8402BACD_250ED896_0C88B4B1_7EA9867B_47AE9A95_AAF96DBE_43A4472D_C0C72F24,
    256'h88D40CCA_D7575333_E5E48F00_BBC1F91E_5EEA7AD0_29C21314_1EE86E77_B99BF0A1
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hF24F6A41_81572048_BE494E1D_FE16A8B0,
    256'hF4D50F76_EB9B2031_5B4A7307_6B7B6609_CE3422B9_2FA723C1_E25118C1_E5B9FD6F
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h3CA72C22_42223CE6_D70F17B4_F4B32818_AA49D125_B4DEFB1F_3C0BE8A2_9BE065C2
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h6D23550B_BC139FF6_461763D7_E966A8A7
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h219EB2E8_EF9F11A1
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h52E6C71A_A23B8864
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h4BBDE099_6949E0FA_88CAD4EC_5CB570FF,
    256'h508DAFD9_33F05E5A_65F507BE_E70E0712_A3A76D21_19889113_A7BE9CCA_000DD6D0
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h6C74ABD4_C4B30FDC_0FE8D84B_302F22A4_1FEE49C9
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h2CCD155D_84FDACED_736E9336_2C8DA83C_5F4DD209_3E4D2A70_DD99DCF4_CCAC341A
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h2F1A2704_F5E21287_FA168AF2_51B370D0_34CDA605_152662F4_D11B3245_D5943EA5
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hFD2E4BEA_016B7911_DEAF01DF_74254737_1445D6E3_955145E3_074D9CA9_E8A4EF06
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA6F14A5C_8FCAC0D6_396E606A_620A9FFB_23756BDA_420A9E7B_D1A7C41E_3A37B747
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hD3D7B758_B37D1D1C_A19A079C_48D7D4E6_7100A6AA_EBE45B6F_09AEFB72_895EC90D
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h876315DB_9AD8BBE6_3ECACE31_278DA3AC_FC873EC5_A22829BD_781EFE2B_4B06F4B3
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h49E0372B_7394D415_D937F357_8CC1200D_D1FB1D0E_CF948594_BC831C3E_0E1F33C9
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h98CABD61_DAC609B5_DD0E0C60_2AEF2E93_2B1FB8FB_631DD82D_E6C9ADDE_7BFB79FB
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h9CC4C0B2_D1AED670_0A44EA3E_7E0610A6_63D52B08_2B9AEF0E_426DF486_6FE88A8B
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hAA3B3B2F_5E3917A7_A7D4B5E5_3C38B3CE_DC40946C_F3635F0C_112F4352_05EF40D4
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hB50CBD86_B4932D75_CEBE7060_738EFA20_35418082_CFE96E5C_C1280FBE_2F2E3236
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h88BCC7EC_BB1A7DB7_BE4CCAF2_7D6EB83F,
    256'hD28156D9_CB50075D_6AF437BE_BB1D8879_E25723B9_D5332388_65874EF2_D375583C
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h209C027D_35C5794F_680B1248_93C22E6A,
    256'h22F5AD2E_7591ECAD_6CCA220D_E3C0051A_862508D4_CE0015F9_376719BD_15980C9E
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h525DCBC7_A2E75C94_580BC5DA_0A20865A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h9B36B012_F2546EA8_45A7ADE1_002B84B7
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h39380023_C25C3DEA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h05C16B58_EFD74310_E6CB4648_037D4969,
    256'hE379CE94_6FA13F67_6CA49D1E_ABA2B24F_B07C2565_82DE3ADB_B30B6045_0F1A18FC
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h86282B72_C315DC48
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h76F6ACFA_65E2F3FF_F25369DF_F7245670
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h4342D7CD
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h8A44441E_74CC34A0_83FB359F_5E5FB893_3C56ADC3
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hA6BFBFB2_EB0038E8_0868A59E_9DD11BBF
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h7449121C_DEFC0BD7
  };

endpackage : top_earlgrey_rnd_cnst_pkg
