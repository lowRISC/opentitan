// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047


package top_darjeeling_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hC2_C82DEB51
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h8573_E042648A_54E4C07E_42D47094_4376231B_1C278894_D1196231_561816A7
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hDBB4685F_7EB27EB3_B35F3527_52E34F64_CE978305_BFC3481A_2162EA27_92B7508F
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h1EAB067A_F954DDA5_491439A9_DDE63208
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h01FDCF25_A4FBA528_39911706_9E77C887
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hF53DDA6F_B4EF8758_B99027B6_AA7468BC
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h0BD8D703_68E7CFB1_1A99675B_14624061
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h9335A9E2_D123834D_18744778_BE5E63C0
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h87E36838_B56B1A45_F6FD312F_5353FA7B_2CE9FC83_DDAF1DD8_C5A42E2A_D24FA022,
    256'h21B6FF5A_AD7A9C09_D5D9FDD1_CFCF5128_35C0CFAE_2ED0C69F_A488685C_EA9BC1C8,
    256'h9BFB7399_AEF5C6EB_5D6E4E23_416A0AA6_D7AC7EC9_C3304470_FBE505F9_649400CA,
    256'h9864FD4C_E49D2CFC_6ECC1025_40EAD873_4700A520_71326894_71AA822B_C51CDD4D
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h37AC2D24
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h83A2B09F_B9D7006B_1534F2BF_7D8EB211_2787B10D
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h46E4FECF_DA2375A6_147421D8_CB69D4F3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hA15FAF83_4CAD515D_76BD37C7_BEC5F33F
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'hDCA11A72
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h848BCB54_640EBABB_89F357FC_C4A3386C_5C73501B
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h0CD06633_6E9B0BDF
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h1EA9DC4E_68352CD1_5D7BFE4F_0ABA5806,
    256'h4ED76F2B_C6650121_523A3AE1_25AE31F2_A5DB0888_CC047EB3_D2710F7B_4ED3C55A
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h8FDCC0A9_5C665A50_DFDB56B8_30A90974,
    256'h761B2E21_6F50D5F9_FBC0ABB1_EDEDB91C_3B11283F_1A7721A5_33B4E812_10C8F668
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hDEC51711,
    256'h0ED2CEB3_1D789F99_6BCD43BA_4FB06B9E_A47DBF44_1AA625F5_DDF2DCB0_3C2B8670
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h432D8B8D_88290C83_734A798C_4C07166D_6157320F_4B202B0D_593A2550_2E9E3317,
    256'h2F8A0578_0974821B_7D6C4172_4585024F_685B3F90_844D9839_1F12487C_0E915534,
    256'h19939B53_5F2C6560_929A6E69_1D6B476A_86233E22_673B8938_421C5170_01960A8E,
    256'h817B5C9F_94522A58_115E2137_0026767F_40044495_87148F1A_773D9C80_1856081E,
    256'h356F757E_0B623031_063C499D_63661015_0327365A_99647197_285D137A_4E544624
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h51A50AC3,
    256'h12C18282_2CF6AD12_452480A6_1092E8A8_0CDF2678_89E06A8A_1AB5F6DB_8158AA7C
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h2A449719_331D97F0,
    256'hD64DA225_A8F19953_2199A11D_02E046FD_267F3073_E1B81470_EBDA4329_1C764023,
    256'h579310BE_651355B6_D9DE9AE0_FA7B00C3_54780CFE_BBD83A81_B270CCEC_5875C79A,
    256'h519017A1_E6769234_16C40537_185EE0B1_C4E32528_95CEFC3F_10C19CBF_42857106,
    256'h46069AE7_E5D927EE_7574F459_0CA97059_2B6E1BB6_D00E2CD1_2ED66157_6720B974,
    256'h8B2BA1B5_154A517A_B0BDD201_8090341C_F1CA49C3_CDA9BD45_6E863224_EE96E2A2,
    256'h766989B1_BA8C6D60_5A860ACE_1728D3E5_A261E054_7E474897_87AAB473_9E281AD2,
    256'h1C17D4E2_135DE270_65271502_2BB23EC5_1FB94850_11C7A45A_10189348_C62DB624,
    256'hE770DB09_5DB23B12_AB49B4B6_8A3A295B_69ED1E55_675014AC_D0B70AFD_0A82B472,
    256'h86784937_315068E6_407A238A_5941EEAE_210B766A_21B9AABA_60363324_24E68BB9,
    256'h293B3030_1BAFBAFE_91AE58E0_92BE0869_C43EDD1F_C3F0CE7C_4F2758F5_CB8FD923,
    256'h9958AF09_E009E61B_2B6AE959_2192A940_D8199C08_68AB9786_F845E901_C37C44FA,
    256'h7F555C67_133B43C1_DE622085_A04820AD_CFD17E22_6A906422_DC713045_959C03E3,
    256'hA5716289_1368DA6A_5984C9B9_52552909_B6D3A120_9C5EF892_1CA3C9F6_0E9576B5,
    256'hAFB45249_9AF36262_59300539_046A3232_425740F4_6A6A7097_8EC61492_CA86B283,
    256'h5A040ED9_1F16975A_0E22826A_0A9F3CD5_A86CA158_0A25BD3F_8505350A_7E628B47,
    256'h96972A14_EABEB146_12379CD4_4540A4F4_8C518AF5_F869AF61_E112F252_D8611443,
    256'h13EEE822_72018C27_E9EF9E4D_73187E07_D37A6567_B825F3AA_D7A04AA9_75684956,
    256'hB1770B26_69B6EEF4_0EC329DC_EFA9EE9C_5512929C_D761D57F_C65BD52E_53D51220,
    256'h11AEC746_864BC719_E64C8B13_8E250427_8A018984_29800CD5_C9972601_55C5B125,
    256'h59D18708_3C58D2BA_732C2788_312B7ACB_5400ECB8_EC54D6C1_BE4CB7D4_7D77D884,
    256'hA16AB790_4485F39C_61FBACFB_38241298_D5465D30_700C316A_87A27F64_694A48E1,
    256'h8E10DBF9_BDB6E830_04F6A685_670487C7_5D7010A0_4A41BC30_1D20D5FC_1ACA9C08,
    256'h0BEAB502_24080A7D_4BEA69B1_530D3020_25BE4693_0520BE45_0D2AAA18_B3DE0366,
    256'h858C16E9_50E73DDE_E85A7B47_8DC394FF_5B65662C_8DB0D44C_14A7128C_F2145879,
    256'h1F1848C3_85DF0AA4_3E442539_1091525B_C002155E_5AB876E5_7431A93C_F06D0393,
    256'h44EB9166_0B02553D_56331107_3022B7B0_BA8709AB_1ED48B07_82C5AC04_105038D6,
    256'hB2D98C7D_0E72659A_942CC28E_9B0ADF4E_D3A829F4_05A516DC_C7B56332_D8C17F9A,
    256'h7775F8B8_980324BD_880DF45E_742B2EA5_D6F14048_FA3A395E_9115B22E_8EE7667D,
    256'hF24C9B31_20132EC4_2270812F_02EAB073_7691B4F9_F7375A66_C2076589_23223737,
    256'h86828EB8_502C4714_B863CB35_0C2DBFD0_2C0EC966_E96C0561_5C258A3E_9D8BC28B,
    256'h20317457_C80497A0_2F0A880D_44D95A91_84632359_EB101ADB_995D4A00_C9634E63
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h2246562D,
    256'hCCEDA3A4_23366A80_96B121FA_42246B6C_385A5AA3_B4FE9C0A_8D1F2128_E03E0B01,
    256'h632E027E_34C81340_BCFD0FD5_3473B544_0B76763B_45BCA816_6865FDAF_59F386D5,
    256'h174CC7F5_FD1F544B_3A82C54E_1481730F_66854723_D0056094_5B6C126F_FEC03BF1
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hB9C2273F_03A025FF_456FAB7C_566BF4E4,
    256'h74544FB5_98D73902_34BDDAC6_888C0DE1_B6499401_13E969FE_CE0A7725_EB8C086A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hF8A394A0_94C63C8A_F070919C_D8B168CA_B6A734A2_A92B34BA_17C53191_1E20C1A4
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h96592784_AC089E72_877BDAF9_F7954486
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h164B58EA_68F9B7F6
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h47CDAFC1_C9A905A7
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hDFC0E31D_C106C730_1A9ECE4C_BD726063,
    256'h858DBA46_554F47F2_7928A122_D3BAD9B0_6B99DA7F_091D7028_BF9094FA_05F7B52A
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h3F4D14A9_62F03037_66EC0934_5B538DDC_A7F43E15
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h6E77B99B_F0A1BCD6_7FB8941C_331A4427_7BC08F71_1D2D33E7_2BC40A36_399D8364
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hDCD59508_D525078E_802F91D8_583804FD_E71271F1_738C1CAC_987A6B8A_7758B762
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h216EDD63_070949C7_834AB6EE_6E7AD485_FF3CA72C_2242223C_E6D70F17_B4F4B328
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h18AA49D1_25B4DEFB_1F3C0BE8_A29BE065_C26D2355_0BBC139F_F6461763_D7E966A8
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hA7219EB2_E8EF9F11_A152E6C7_1AA23B88_64416E75_0C01A333_9C6C7AA1_1244ECD2
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h8A62CB1B_851078C2_A5F18EEE_28D0B562_043B7312_EFAD871F_92E7527D_A865D661
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h281FE98D_FCD72E3C_6D150A85_D6300959_6F7966C5_C68CAEDD_E4AB7C65_FB8D5961
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h8284064D_7194E470_7ADA81F8_A6DB14CA,
    256'h845BEEE6_0798289A_D4FB0DF1_76829639_0152700E_078EC5A9_51B627CF_2CCD155D
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h84FDACED_736E9336_2C8DA83C_5F4DD209,
    256'h3E4D2A70_DD99DCF4_CCAC341A_2F1A2704_F5E21287_FA168AF2_51B370D0_34CDA605
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h152662F4_D11B3245_D5943EA5_FD2E4BEA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h016B7911_DEAF01DF_74254737_1445D6E3
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h955145E3
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'hB8DC8828_B693F443_70580F72_C69E2BF6_FF4ACD20
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hD3D7B758_B37D1D1C_A19A079C_48D7D4E6
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h7100A6AA_EBE45B6F_09AEFB72_895EC90D
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h876315DB
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'hB231FAB1_4970DAB0_74417C8B_E8522436_B27E5F73
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hC1200DD1_FB1D0ECF
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h948594BC_831C3E0E_1F33C998_CABD61DA
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'hC609B5DD_0E0C602A
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'hEF2E932B_1FB8FB63_1DD82DE6_C9ADDE7B
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hFB79FB9C
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hD8FADCC2_3252EE62_5133F158_203CE80B_B95D5BF8
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h17A7A7D4_B5E53C38_B3CEDC40_946CF363
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h5F0C112F_435205EF
  };

endpackage : top_darjeeling_rnd_cnst_pkg
