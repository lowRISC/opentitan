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
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h50_8E576E43
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h7DA5_DD443190_81848F24_210E8DE8_A498830A_0015672C_74CD6E11_6559C654
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h986313D6_12FDCD62_AFD0C3A5_FC772CEB_91C16F5D_6E17DFF0_661BFBA6_F4E0571E
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hAE0FC6E6_A1A665F0_42709B54_CB121F70
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h02A405EC_DCF1FEB0_FA7A1487_7EC88637
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h87AF272E_FAA51F0D_E710C891_D47FF720
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h9F95D614_848E3836_1CD9B7EB_23D532C0
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hAB44E1E9_2CCFEBAD_AD9193A3_EE4ECD8C
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h032462B3_E18549CB_1E70D5A8_3DE6673D_2C1C0A7B_55176264_E55C329C_8AE4725A,
    256'hEAF67281_50127AC7_55D70063_277642B5_309A1639_90B966CD_494444C3_BCDF8087,
    256'hB7FACD65_E9654CD8_5BC66D10_208C4FB5_1B97BBF4_D12C378C_CFD6A5A5_BF3032DB,
    256'h51FA1EB9_2F6CE10E_90F9C5C0_6F733DC9_11A321DD_4C0AC240_6D467215_DAB3F2B5
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h4A52E672
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h1626CA23_5B3B6C12_4BFE5E54_EBF4A934_783055F0
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h55E0F815_0242862E_B20EEA9A_1F754471
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h6551512A_112DED67_8CE824A0_8E29C772
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h795A358E
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h44CFC8B5_8B712090_29F2B7FA_22DE86DE_7D5D0C38
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hD1095889_FBD8A7B5
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h392FA90D_E595FF71_3B4289DD_4E117922,
    256'h432F2804_49DB5525_06281AC8_698B62BB_B13CDF02_B73D2A71_B8D7F7AC_191F8B1F
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h03E5AB51_C865BF6D_4DDC1EB8_653F3233,
    256'h3B7DFCA2_4814FA1F_11D61B09_5A971EC8_101B4C0E_8D14A793_92E689E6_A9C6EEC3
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h82FA14A8,
    256'hF2B75C26_5C9CB3B2_F1C44A72_87AB4C06_18822E92_A084A048_FFE9FB86_140A79D3
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h70666885_3241427A_1D566559_0D530C47_458C2397_5C21863C_917C5160_37078324,
    256'h8B9A7F93_73627706_5A392F1B_8E7E6F4E_81118A1C_79589D74_042B0817_710F252D,
    256'h48648819_2A2E4900_4610129E_1A319228_8257843F_894C090A_50695440_616A1E96,
    256'h6C362038_144D1595_35346D02_875D9C18_754A268F_0B015B1F_78137629_9827220E,
    256'h9F7B8D90_437D4F6B_3D723A05_63996716_9B30446E_52942C33_5E033E3B_5F4B5580
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hE933D88E,
    256'h2E1CF654_60F23FB7_80499E6F_CCE64CEA_FD282C0E_33FD2C07_986C2A51_1755F072
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h99E8E296_3E89488B,
    256'h131D0C87_2324F634_25F3CEDE_85EF7490_761B0EC0_AD251FC8_163069A6_5313C5AD,
    256'hA542E455_D553AEB3_7506368D_F89C1876_C38C3186_C6AA35AC_ED838342_B42D8471,
    256'h88A8C868_5C27895E_B4905481_AF5DE7E8_7210799F_63A6AD13_88D0561B_49C2A1E9,
    256'h9B876359_2CAA899B_B52E072E_92BA9A20_ABD6235D_97AA5183_C30F09CF_F5BCDE2D,
    256'h5B6AE2E1_7B9347DD_7C97164A_698E620C_B22E087C_2318B809_0190182A_A8262847,
    256'hC4F77240_A1453AB1_8BF07857_400BE5BB_0D07C504_FE02279E_C0FC901A_03EC0C33,
    256'h9A18B255_4D68DCB1_9079BEEC_0C1C169B_D569B628_26ACE962_B26FCBB3_E4B11019,
    256'hEBE0A119_B149E27D_A4222AC4_5F423012_3306A30E_E28244BB_52CA91B2_7F56C759,
    256'hB0625D13_1A005F6F_F0956988_6C5932F6_B70D2345_CF83128C_7C9426E6_B049D957,
    256'h5EB1A899_5D16A728_E190ADB5_547B2E66_17E6D750_DA619DA7_216BD1B6_5D6AD934,
    256'h8F1699A5_43925E3B_DD8039A5_180002BE_B529C963_8B000C19_271EE67B_5C65C140,
    256'hB94D65E5_1B602125_9CC0A71E_5476C36E_9ACB0AB9_60504A79_1C6426C9_D1B4A1CE,
    256'h8ADC622B_1D7C0A50_195B377C_6B4D824A_FE9391AC_1B4DD07D_4A621871_8B56151D,
    256'hE7868FC3_8F17C142_9106E97F_1CD398B0_8D0A4BEA_FD13C217_490C355A_09048A6A,
    256'hAFE0A1C8_04DBC939_CC98F102_1CC45DA9_2AF8A3A2_CFE6E670_6C6D4A9E_3C804925,
    256'h40CA1571_911D2252_A83AEA43_44603C11_60A089F3_615C82EE_88B0D370_D2AA5A49,
    256'h161E14E4_802BAEF6_0A8FBE6D_912A6094_4CC0C68A_1F6B44CE_CD074491_79A8516C,
    256'h9825E403_CFBC557B_A75FB314_C25D4526_6910A857_1900C3B8_19D2F19C_8DB0A658,
    256'h0B7E9097_A1993CA4_7860B358_C4885037_0047E2D8_8474DD42_8B1E1D4D_C88E5927,
    256'h1F49D408_8A44BBB0_0D991126_54E72DE2_FB68FD3E_A3A9E50D_B7C35521_29ADA65B,
    256'hA93C118C_7512056F_90A65093_0650B532_F56B93B2_CA4D008A_883EB3B8_8898CA45,
    256'h49966275_7FBC2CA6_D58D1B81_07C83D41_E7C43E94_B6224A61_5A544363_645C4F82,
    256'h660DF8B1_EBBB2F13_69054A44_058FE1FA_AA2B9ED4_9779E94C_15F6DDDD_1D1CE8ED,
    256'hF3B3F08A_7C5AB40C_F08B1BA9_43B06DB8_6897395C_5BB20B89_88429683_C20985A1,
    256'hA89712F4_92914564_637BCEB8_102CC3A7_A7A98F6F_4CD9B92E_7FA55485_547FD3D7,
    256'h06523D1E_31E23323_A1962903_C4A0605D_3208E885_18CE662F_28361554_97245CE5,
    256'h9207353C_F5132691_5AEE9D80_CB90A99A_87725ED1_702304D6_AE4E16D9_C64FAF21,
    256'h30E941A3_5DC47E72_20CB4A5C_04C26D58_DD166101_C14EE740_99F61D13_114436A4,
    256'h70174ABB_5A5B94E9_B1BEF156_0208F6F3_5E091AAD_19596391_851E3827_F00C591F,
    256'h0C1069E0_3E2B03A9_42768D4A_0039B8E7_723D1A87_A85A81C5_B31370BD_2F4B44DB,
    256'h765601CB_D04673AB_16885AA2_55D7E54D_915E8143_6F1CC2D0_EBF15BA0_444C4638
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h46C49F15,
    256'hA16A2A1F_D01F8E09_D92DD13E_0298799D_91C54BFD_2A51F45A_ADF344C2_62BB0ABD,
    256'hE9B240D7_63DA6C42_50BA5A44_A7D4F4D7_F99B4A64_80DA2D53_E7CA1520_1A8F5653,
    256'h0010117F_58C9E994_6C111804_07FEB471_0F404E6E_4FACE59B_972D1FDC_AF711C05
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h1ABBA9F8_CE16CF92_D4B5C3C2_6435ECD4,
    256'hDDE06154_85C5D6E8_9BB244D3_D7F0ABC0_641D3467_86323688_ABC0EB2F_E541E39A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hE24BE7E1_C96737B7_26A4C6F0_4993B3E6_AAE70F22_AAF748B5_7C320264_E157E2C7
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h4A280332_61EE6CEC_10075C55_A820F842
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hD43EE1AB_1B3D78F9
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h92D22346_9898EB2A
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hBA87C33D_D8319DE0_A103ECEC_EAD96923,
    256'h98EFC95D_9B938350_5FC4B550_B9B459CA_A265A3B0_311F5824_12AB4C5E_C71371BF
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hBCE26820_3CC807B4_B242F394_F262A5B5_35F3F5AB
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h5E456F3B_26D15F55_84BB9879_BD249785_2C23D0FA_289C3348_CE364ED5_34970E1F
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hD45EC606_BE134FC0_8318BD29_B22B08DF_647BDC30_068E7513_200FA828_BFEE3ECC
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hF02417FA_68D00453_4267F60B_34A8F072_E77EE485_9B243F92_CEB098BE_6E65C359
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h480858C3_9611E658_C97FB8D3_E9CC0E7F_8FA87252_00C726C8_F90EF5E2_B74BEEE2
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h7CFA19EA_576CA8A8_225C8E17_053E44B6_8DD7822A_6859F2CF_52A55FD1_81B082D0
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h3C583756_F11AA5B3_7F9544C4_AA90EB97_E1C0F808_6F627A28_1C5681D6_566641EE
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hCCCC8887_6AD113C5_0AD1BE4D_94DCE8FC_A54128A3_860AE1D3_493FBEF6_B9BA5DFE
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h4463A461_5EF46762_A794A8C2_597E69FB,
    256'h259B9619_14CD75BB_FD36BA48_E780D27C_D582540C_7A68FF25_4EDFD852_829FECCC
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hABD4AF9C_9032DA20_BDAF59FE_2AE209B8,
    256'h325D2C8C_35FC9606_79B106A8_7E59E6AE_B1B5302D_33401070_251696FB_B4BA169A
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h6CD82FAD_46A0A5C0_4009BB93_4C7EF7B8
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h3B6E4061_0B4309FC_B9DC54D4_276137F9
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h901D09A7
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h1036ED2B_E8B646C8_24A692F9_5F1031B9_DF89D3AD
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hE927F6D9_E4ABAC39_8D42C745_EEF646C1
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h464DCA86_DAFD7C7C_71E6058D_DFD871C5
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h1CACBAF4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'h2C32AE93_87FDA299_E9CCF52A_BBC8627B_4D8D8028
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h6FD468A7_7EFDE3DE
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h5B4CAF47_76A247BA_BA4C9908_ED16BC54
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h15EC16D2_8C535513
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h12FCEDCF_2832A66C_EACF8ED4_D5B61617
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h7DD43B56
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h1440B451_B8D70817_96663DFD_BEE6D283_2AA1A5DF
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h74F35C79_F397C4E4_C7E22B75_81848A90
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hA1254B22_76BEC9FC
  };

endpackage : top_darjeeling_rnd_cnst_pkg
