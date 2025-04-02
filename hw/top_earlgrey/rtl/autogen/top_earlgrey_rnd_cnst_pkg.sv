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
    40'h50_C2C82DEB
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h8573_E042648A_54E4C07E_42E77094_4376231B_1C278894_D1196231_56181694
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
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h0CD06633_6E9B0BDF_6A55F0D2_3BB7DC0D
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hC524D3B0_55460356_21885527_94DD2BEB
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hF67F318B_5A490E55_F7D8B832_5652A924_82CC3446_8C37BFEE_731A0AB4_30181CDE,
    256'h15F40D83_472DD252_E38F2C5E_24D201BD_B435D5CF_F95C40A1_643CC8F5_40230522
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hD33A4EA4
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hB16325F5_4D0ED9E3_1C04C3EB_9D5F8812_7F41CDD0
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h4922F7DC_57CC668C
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h5D273257_0001B22C_5987AD3E_90B08F80,
    256'hAE6F3B8B_ABFF36EA_27B45FD9_341AF677_B50C416D_36562374_7A77A083_06526F16
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h386FA841_1F6AF130_D92E9B5C_863CB0C5,
    256'h4916B172_26009147_BF88B694_AB9E9DAD_F513B360_6DD7C2D2_B63FCCC0_4F495EB9
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h4660C443,
    256'hDF8E6E3A_14E92AF0_B0266DCD_3DE77D58_92992045_3CEDC4BB_4632D2EE_9D3B62DA
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h04865797_42011B23_24800A7A_7215902B_345B2662_581C0C51_0F680B9D_4A1E389C,
    256'h1F6D5F07_02473073_32431D33_17362092_6778039E_8C3D4D8F_6B843B55_897D0E96,
    256'h7631747C_19692E7E_29915E63_1A8A4C3E_2C5D9A45_35853C13_9454496F_83407722,
    256'h66561664_93600961_05522875_5A215395_2A442539_79598812_8B3F5C82_9970379B,
    256'h7B8E816E_11711018_4E4F146A_2798506C_3A008D41_06088746_652D0D2F_9F4B7F48
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h4FE255B1,
    256'h3D5003AE_3828EE1A_34F865C1_0B37A68D_F5D12932_05F54724_A965AB81_CA6C3169
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hA1114968_69A41CC0,
    256'hBF1BADF1_C3C4F89D_1806DD54_34EEB721_AB6CB040_35B8112F_F4494614_F0E622AC,
    256'hB24F636E_878961B9_2D2026E1_FBDAE234_1255B228_8EE7921D_6585DF74_1EB12B0B,
    256'h0B1098A4_D6125F1E_9AB15A59_F1B72EE1_E9017063_E9591888_DE690E31_AF9C7B76,
    256'h325A4629_CD5651E1_98CEA106_8D100417_35C00635_435BC83A_C150BD20_C49265AB,
    256'hDF4C1C93_1DDB5319_8F332D53_1C355668_B6599C60_466439D1_11B02965_FE516D33,
    256'hE9CD27D7_2A889517_DDE26AB5_4641C8F7_00A7AD78_FE54611B_3408A2C7_D5747DAA,
    256'h4A2770E1_F530CECA_6C29108A_1B42BDAA_5867240A_A251A544_8001ACC4_AA0B4883,
    256'h61CCB32D_4E409538_C66884B4_90486F83_36B64C9E_E0D05544_E517DAB4_2303F71A,
    256'hD883A673_FE354F53_96EDCB84_496BA94F_42AE0912_6F915790_89D7924B_DC35272F,
    256'hD9350854_2F8E5549_9775A347_6D2C89E2_C73D74A7_56A168B2_47488299_9FAC8211,
    256'hC97E2954_C6A1046D_15372AC5_7C8FC3D2_7DA991CA_CC185545_71D5C00F_8E78C213,
    256'h40ECD121_903F9481_9EC70C57_66F0E217_4030AA7A_902725C0_50053052_ADBA8AED,
    256'h46528D81_92E32EB8_6746B2E4_1F698608_71ED9BAF_78354009_8A87AD3B_7E66BBE4,
    256'h1EB9DFC9_04162E98_B932DB8D_8745E987_049AF3D5_5DA18309_86DF9B4D_A738DDBC,
    256'hC24A0534_04D36A0D_C30444C8_48FB42E2_E3387B74_06D2A6E1_136A470A_E480D1BB,
    256'h99BEB209_4C062605_66608E5B_B3C0B1B0_C08502C8_1C1B20AA_A45D636B_6CBC5833,
    256'h9197B970_CA1BA398_106F4248_1526FE67_8519A479_45A8F630_0F7567C9_280C216C,
    256'h09C03B61_59BC417D_434D837E_188AA989_A2764005_E2770B85_B14801A9_C22BA246,
    256'h47160E0C_2AA3961F_FA44A721_9B12E1F0_0E98922B_185F2BF6_555CB962_06E56664,
    256'h67F90AE3_804AFB49_0C7F65D8_85AC4AE2_2589054D_4EA561E8_B39E11F5_E5A80F93,
    256'hC0523C9C_43B60213_910C4923_5116DA2A_CA3CC78C_75A70771_1455E0A5_40947AB9,
    256'h825DC2EE_FB60C656_66641866_C105A10A_0E82121D_95EE93BE_485688E2_8DB0A707,
    256'hC3994BB5_B0F2DDA2_4C4392D9_11BC108C_32BB7910_FAA070B4_6AE41960_27294579,
    256'hD3934EBA_69BFC0C4_05FEC67E_CEE68C5B_6683C5C6_BC18ED91_A1B6324D_EBF21A53,
    256'h8E11FC02_8B6F2316_387768E1_5A15A4A7_10644A76_5D45DC5C_3668052A_82505269,
    256'h88F7321E_F5E2E853_4C4124D2_3F42B2D3_06B686A7_7CBC3083_D7CCD594_8326968C,
    256'h02092AAD_642B4070_DCB1282C_24E9E24D_D6B93A1E_266FA352_5378EEC6_60AAB0C8,
    256'hF7693EB0_4E37A84F_59EF111E_7E2BA750_4309192E_D3A4D67E_317305D8_89260A7D,
    256'h6E6084B0_39296F49_E22D5B09_D73BF5EC_64A7BA16_977164F1_DA556825_E74AA75A,
    256'h2507A58A_7E805234_CF98F135_D53C0118_EB7A0F16_47E6902E_79C898E8_438DD338,
    256'h41AE82A5_FA655F4F_C2D8162F_BD6A5AB4_718F0A44_C31A8202_0372EF8A_4454BE78
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hB6396FCE,
    256'h53002A29_61AC84BD_DA1315AD_D2F8A394_A094C63C_8AF07091_9CD8B168_CAB6A734,
    256'hA2A92B34_BA17C531_911E20C1_A4965927_84AC089E_72877BDA_F9F79544_86164B58,
    256'hEA68F9B7_F647CDAF_C1C9A905_A7AA52EF_ED17F8EF_A13E9543_502F28C0_2C460AA8
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h8CC0F8C7_60851B07_167C7D4A_3D3A9910,
    256'h042F637E_4D24B960_F95691CF_A5DE9E44_A287B22C_F4EA3F53_C6C1AF2B_66B9DA74
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h88D40CCA_D7575333_E5E48F00_BBC1F91E_5EEA7AD0_29C21314_1EE86E77_B99BF0A1
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hBCD67FB8_941C331A_44277BC0_8F711D2D
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h33E72BC4_0A36399D
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h8364DCD5_9508D525
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h30DC4F45_7678D15F_06B4A033_4E724386,
    256'h5C2C7E9E_8553242E_BE8EFD48_2DEA6C86_3976269E_9AB1FED5_C13F396D_A42E08C1
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h0A1EDDAC_A974AF00_44D9E1C6_AF0B1699_295FF74C
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hCB1B8510_78C2A5F1_8EEE28D0_B562043B_7312EFAD_871F92E7_527DA865_D661281F
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hE98DFCD7_2E3C6D15_0A85D630_09596F79_66C5C68C_AEDDE4AB_7C65FB8D_59618284
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h064D7194_E4707ADA_81F8A6DB_14CA845B_EEE60798_289AD4FB_0DF17682_96390152
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h700E078E_C5A951B6_27CF2CCD_155D84FD_ACED736E_93362C8D_A83C5F4D_D2093E4D
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h2A70DD99_DCF4CCAC_341A2F1A_2704F5E2_1287FA16_8AF251B3_70D034CD_A6051526
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h62F4D11B_3245D594_3EA5FD2E_4BEA016B_7911DEAF_01DF7425_47371445_D6E39551
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h45E3074D_9CA9E8A4_EF06A6F1_4A5C8FCA_C0D6396E_606A620A_9FFB2375_6BDA420A
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h9E7BD1A7_C41E3A37_B747D3D7_B758B37D_1D1CA19A_079C48D7_D4E67100_A6AAEBE4
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h5B6F09AE_FB72895E_C90D8763_15DB9AD8_BBE63ECA_CE31278D_A3ACFC87_3EC5A228
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h29BD781E_FE2B4B06_F4B349E0_372B7394_D415D937_F3578CC1_200DD1FB_1D0ECF94
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h8594BC83_1C3E0E1F_33C998CA_BD61DAC6_09B5DD0E_0C602AEF_2E932B1F_B8FB631D
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hD82DE6C9_ADDE7BFB_79FB9CC4_C0B2D1AE,
    256'hD6700A44_EA3E7E06_10A663D5_2B082B9A_EF0E426D_F4866FE8_8A8BAA3B_3B2F5E39
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h17A7A7D4_B5E53C38_B3CEDC40_946CF363,
    256'h5F0C112F_435205EF_40D4B50C_BD86B493_2D75CEBE_7060738E_FA203541_8082CFE9
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h6E5CC128_0FBE2F2E_323688BC_C7ECBB1A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h7DB7BE4C_CAF27D6E_B83FD281_56D9CB50
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h075D6AF4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'hAD901D2E_6DCC8E0A_0B857260_CDE3FD22_9F11FAE6
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h2E6A22F5_AD2E7591
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hECAD6CCA_220DE3C0_051A8625_08D4CE00
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h15F93767
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h439BD600_F9899F5F_7D258135_BB4B145A_B8198AE3
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h380023C2_5C3DEAF3_8D871A3C_5213602C
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h32E73D30_51DB61B7
  };

endpackage : top_earlgrey_rnd_cnst_pkg
