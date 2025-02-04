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
    40'h51_9D69C705
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h85C6_4A39050B_7534A78C_F5C07A40_49443355_94C7C76A_012209B2_18985586
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h7EB3B35F_352752E3_4F64CE97_8305BFC3_481A2162_EA2792B7_508F1EAB_067AF954
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hDDA54914_39A9DDE6_320801FD_CF25A4FB
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hA5283991_17069E77_C887F53D_DA6FB4EF
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h8758B990_27B6AA74_68BC0BD8_D70368E7
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hCFB11A99_675B1462_40619335_A9E2D123
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h834D1874_4778BE5E_63C087E3_6838B56B
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h1A45F6FD_312F5353_FA7B2CE9_FC83DDAF_1DD8C5A4_2E2AD24F_A02221B6_FF5AAD7A,
    256'h9C09D5D9_FDD1CFCF_512835C0_CFAE2ED0_C69FA488_685CEA9B_C1C89BFB_7399AEF5,
    256'hC6EB5D6E_4E23416A_0AA6D7AC_7EC9C330_4470FBE5_05F96494_00CA9864_FD4CE49D,
    256'h2CFC6ECC_102540EA_D8734700_A5207132_689471AA_822BC51C_DD4D37AC_2D246C42
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h64F37EC1
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h85DEBA1D_C1C69914_9720B1B7_E429BFE7_47590893
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h21D8CB69_D4F3A15F_AF834CAD_515D76BD
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h37C7BEC5_F33FDCA1_1A72DC05_A2313B71
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h8E6D6DBB
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h716FD82F_E16F8D3E_6C4FC8E9_2A914703_136D2311
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hF0D23BB7_DC0DC524_D3B05546_03562188
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h552794DD_2BEBF67F_318B5A49_0E55F7D8
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hB8325652_A92482CC_34468C37_BFEE731A_0AB43018_1CDE15F4_0D83472D_D252E38F,
    256'h2C5E24D2_01BDB435_D5CFF95C_40A1643C_C8F54023_0522D33A_4EA48571_9E18A080
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h49CF1240
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h013CAD1D_7737E78D_C6542B6A_C707227F_130476C3
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h99531A32_21A2EDDC
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hE2883DAE_AC36E410_17C996EF_58C392D1,
    256'h42C257C9_3A888FF3_72128F24_645FBB54_D06A69DE_FAC0C417_1B4D97B6_378DD1E9
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h6454A32E_11837305_65A4E448_DE6A01BA,
    256'hD1ECBC9E_14916C97_436013AB_ED798BCC_4AE9E9DA_F7B10F36_06DD7C2D_2B63FCCC
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hE92AF0B0,
    256'h266DCD3D_E77D5892_9920453C_EDC4BB46_32D2EE9D_3B62DA48_7F4BA0D8_482F0D2D
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h8F242B04_90631533_8E4B0F42_78749947_235C0A39_3D4D671B_5136261C_4864940C,
    256'h851E0B97_777F1F7A_5D070268_38848B3B_628C5888_17662096_0E763403_2F937D57,
    256'h016B4332_5F1D306D_313F2D9E_8019862E_374A2998_926F1A91_4C3E552C_69790D45,
    256'h35893C13_9B54497C_9D401222_72561670_9A600961_05522875_595A2153_9C2A4482,
    256'h7383257E_5B8A5E7B_95816E11_7110184E_4F146A27_9F506C3A_008D4106_08874665
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h3828EE1A,
    256'h34F865C1_0B37A68D_F5D12932_05F54724_A965AB81_CA6C3169_9E374BCE_117DD74F
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h11113C08_9F84E7AB,
    256'h82ED36D4_87FAC024_D8F18B1F_BF1CE6CC_83961DB0_362714D4_FC0E468B_AD589945,
    256'h6F0B03C4_AC0BD654_E52119A6_C1DCF670_9B570EE3_C5CF8B69_D721C691_E9845896,
    256'h9548CD50_CC35E640_AAA144F6_73866118_AAB4346D_F7289871_D0E80553_34E87AC6,
    256'hA09A695A_263D800F_F4BD76B6_C9B8D98D_86D6CA29_24069720_0417A900_0959474E,
    256'h0A28AD80_9960E16A_72C45702_56D64A9D_E88594BA_2D884835_25CD7B05_CD119FC9,
    256'h6D876BCC_CC2AEA6E_AC7BC6B3_17D1499D_224701C8_7D276A89_A41E476D_DB844A20,
    256'h551D1AE8_C64B2170_E1F2C611_931D6F8D_029108A1_6A158AB2_CFBC9CF0_29F64751,
    256'h820006BB_24B81125_0D9EE1CC_B32D4EC0_95F9C70D_09089039_2FBA799D_AE1F50D0,
    256'h55556B6A_DCFA2303_F7316181_DBB2CB07_4C902702_8D99096B_4AA14B59_7A4AE442,
    256'hAE7089C1_914BDC41_FF2FEB95_18542F8E_54059C9D_91AC5233_A1956480_8829A39A,
    256'hD4211CAD_7295506B_5047C557_74277544_FC3D2BDA_A51FC154_2062AF15_C757183E,
    256'h39D819E5_03B40487_B4FE5306_74A2610C_57A798E2_174030AA_7C566745_D0500530,
    256'h82AE3297_1868A28F_C6D2E32D_A69046B2_E41F6AC6_0AC9F49C_2FA89540_098A85A9,
    256'h3BB4E1C6_4C1E95D3_590C162E_99067EFD_B20745F9_8B049B43_D55DBE43_0BDD969B,
    256'hCDA9FCDD_BD824B95_3404D36A_11C90444_C7ACFB42_E303387B_7586D2A6_7D136EE7,
    256'h21CBB891_BBA5F062_2CB25304_8D4159A0_239770D0_2C6C3021_60B22206_C82C5517,
    256'h58DB2B3B_190CE485_ED053286_E8EE061B_D0920549_C059E146_6B1E516A_458C03DF,
    256'hD8C64C03_085B0E3F_0EDBE615_9BBE17D4_34D837E6_D8B29B9A_A784005E_2770E862,
    256'h3E835A98_31F72464_9162BB38_29CA9A5A_A2E9329C_866C4B87_A03A6248_AC2D7CB0,
    256'h99557251_82DB9599_91A0644A_6A032BE8_E430EAB2_A236B12B_A0DD5B45_E11F5E5A,
    256'h8CF93C05_23C9C43B_60213910_AC123511_6DA8ACD3_CC78115A_7076A845_5E0B9809,
    256'h47ABC825_DC2EEFE6_0C656666_61866E10_5A10A0E8_2121D966_D43BE4A5_688E28DB,
    256'h09507C39_94BB6712_2DDA24C4_392D911B_CD08C3EB_E7910FAA_C70A22CC_41960272,
    256'h98579D39_34EBA75B_FC18405F_EC97ECEE_68C5B668_3C5C6BF1_8EDC1A1B_6324DEBF,
    256'hE1A538E1_1FC028B7_13316387_769015A1_5A527106_44A765D4_5DC5C366_8052A825,
    256'h0526988F_7321EF5E_2EB534C4_124D23F4_2B2D309B_746AA59D_F2F0C20F_5F335652,
    256'h0C9A5A30_0824AAE5_90AD01C3_72C4A0B1_53A78937_5AE4E878_99B84D49_4DE3C799,
    256'h82AAC623_DDA4FAC4_38DEA13D_67BD0479_F8AE9D41_0C3064BC_0E9359F8_C68C1762,
    256'h249829F5_B98212C0_E4A5BD27_88B56C27_5CF007B1_929EE85A_5DC593C7_6955A097,
    256'h9D2A9D68_941E9629_FA0148D3_3E63C597_54F00463_ADE83C59_1F9A40B9_E72263A1,
    256'h0E374CE1_06BA0A97_E9957D3F_0B6058BE_F5A96AD1_C63C2913_0C760808_0DCBBE29
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
