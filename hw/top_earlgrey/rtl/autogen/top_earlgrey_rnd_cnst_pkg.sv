// Copyright lowRISC contributors.
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
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hDD_23F39863
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h1639_50266199_4CF48D44_01E17DA3_88916781_55C2940C_C8028976_CB7589C4
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h2EFAA51F_0DE710C8_91D47FF7_209F95D6_14848E38_361CD9B7_EB23D532_C0AB44E1
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hE92CCFEB_ADAD9193_A3EE4ECD_8C032462
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'hB3E18549_CB1E70D5_A83DE667_3D2C1C0A
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h7B551762_64E55C32_9C8AE472_5AEAF672
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h8150127A_C755D700_63277642_B5309A16_3990B966_CD494444_C3BCDF80_87B7FACD,
    256'h65E9654C_D85BC66D_10208C4F_B51B97BB_F4D12C37_8CCFD6A5_A5BF3032_DB51FA1E,
    256'hB92F6CE1_0E90F9C5_C06F733D_C911A321_DD4C0AC2_406D4672_15DAB3F2_B54A52E6,
    256'h728678AF_0718068E_344D2EAE_4D73C8FA_54DE8AA4_A4F258F3_B2A145FD_1950AE55
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hD693E579
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h5DBF54F6_34C4AFA9_98E470C2_58641E52_39B63C4D
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hC772795A_358EC30F_1BEDD1AF_0EC9D9A9
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hCF36A2B1_30D32AFE_121AF734_F628363A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'hAA0E93D4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hB4D22A55_B8DA8FDF_1790665F_1FE88170_EE09190B
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hDEBE60A2_2DB6D398_D4A21B73_699E8082
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h0434A1DC_D0488805_541166F1_EC8CEB42
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h692B089A_6F99B1A7_AC084224_ADE46129_80D48E6C_6493A50E_EDBAC6A4_6B7A8A9B,
    256'h2C7AEC92_F39E4947_8C398C91_DB184183_1B1F5C82_A556096F_FF6175FC_10F93979
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h2B444E52
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h596AD040_DB23BBA7_D2614FEE_755B198C_99EE0903
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h265C9CB3_B2F1C44A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hD3BC5924_88AE0CD2_907447E3_AE96B296,
    256'hFF27DF01_FF5AD63A_45B53833_D0263CE5_F3B15E5E_085D52DB_EA242E01_814EA85C
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hD33F4E8F_C1287D2E_BE0C6222_9F05DE87,
    256'h8CAB6026_79355C5D_9375B66D_072A98AA_6C681B8C_D65ECB14_0FCF254B_D344782D
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hEE55B032_C07A29B9_20B7953E_485F23AD_102C6A0E
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h0C6F8794_5305816A_0D5D109B_5C4D2235_0F7D3457_2C06679E_483E4E80_291A6B97,
    256'h8D846D61_1D649572_44137E31_924A8A04_1C437F58_23256290_8C5F6901_54279138,
    256'h41092D55_9C49705E_32866302_9A1B3A9D_42182B20_33503F79_082F7576_3D39730B,
    256'h287B369F_03687807_16148566_374F2440_5B1F302A_0E8E476C_7A749615_1E884B0A,
    256'h56774500_8F269352_2E115112_5A3C1789_833B9959_827C1998_6E658B60_4621714C
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h165EE14A,
    256'h00EE9FF9_382AF33B_47971855_8E675976_4645AAD1_FB21C181_24635E3D_50A88F68,
    256'h08045627_AC18F377_D9071BEC_A6F194EF_96F3E535_B58F2ADA_D82B175F_E9EA1C32,
    256'h6A6610C1_117744DE_61CCBFAB_D3E1FDA6_67E04082_478C14DB_070A6129_BB2945B8
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hAA611A06_4C05044A,
    256'h68A00AAB_6B006462_49809DED_20300415_7D5BF189_716117A7_8A410604_6644366F,
    256'h9DD15146_51B68881_9D2FB35D_142706A8_68FC34B3_ADC7C3C5_E12A8DC9_08E12363,
    256'hD12DE51F_DC2BE4F9_620C6AF4_72036211_A4E95584_00C9C371_85749143_9D5B6082,
    256'hBC740A29_84B16EC7_D39DA3AD_6E0BE2F7_84195C6D_9D6F25F3_0D925380_A3FC9948,
    256'hD63756C3_5AD7B5C1_58C302D3_4977096B_117F12A7_AEF02DB9_A15EE1A0_D0244492,
    256'h6D9077E0_E3BA7FC7_69C7589C_B8416554_EC165975_35278E17_C61E5EA8_2FAA2C09,
    256'h8619A6B1_1A66CF3C_041E7DAF_D4012C73_0BF96ED6_7E5710CE_EE940501_D4BA465B,
    256'h40ADE235_D5EC0C38_A54ED820_157486C6_C4AD7660_1515EC95_8F75F9F1_64CAE92E,
    256'hAD78018B_A0B65B04_E4C5A85D_0BB87580_6A8C1735_2B9003FA_CED8279A_16071E72,
    256'h6352318C_14A02048_06C50956_7ACC5D47_9C388431_4CB79EDE_A0DCA2E6_DC22C3E2,
    256'h86B05E1F_D344660B_8C9800C8_69E4688E_29376912_04CCB21A_02F8B546_1CB8F239,
    256'h1AA8C976_1B8A1406_A49A3692_84947A96_2653DA6D_0D076216_931B60A5_E996BC2E,
    256'h236D204E_ABA52CE4_4DD338D0_EF3C9A60_38011800_02BDBA29_E3238902_0C168440,
    256'h618BE98C_567C9EE7_94D27A35_A3646EB9_A09D8302_F18951DC_72F4832E_A8818B4F,
    256'hD64B55D3_BD904BC9_1C7A2270_216A074B_73A04881_E2A2B1F4_0BE9659C_6558A660,
    256'hDC6B4D82_47AEE66C_3191C2B8_BF112298_861C4FB6_AD4773E4_43F0E3AB_F1F1361E,
    256'h105DB672_89B2E099_F6AB85CB_09D0A423_EA8B4C4F_8C5F0430_D55A5FCA_13072284,
    256'hA79828BD_4136080F_B05C5BB6_5355C873_11769671_628DAD9C_CFE7201C_0C6BE8B8,
    256'h5DC227E6_963E6C89_25421432_855439D4_11D2252B_04B430F8_8A2C4464_14B62D58,
    256'h2CF27EA6_361AF572_433826B3_4CC24A9B_FBA68E80_C7E71D39_4055D898_58252E46,
    256'h64623C0F_AA8EA72F_03963A1C_07DF70A5_FAB7ED22_94E66197_96CECAB9_4DE84ABF,
    256'h7907BA1E_602406FA_00FDC290_8926ECA9_59FC25D7_9A02125B_0BA9270C_696E91CD,
    256'hF7EDF586_9420D548_8E929AEE_AC82C034_F04631D4_4815BE42_99424C19_42D4C351,
    256'hAE4ECB2B_38022A20_FC0AFF22_717A2926_5989D5FC_F814DB56_346E041F_20F507B1,
    256'hD0FB9E99_89263C4D_5A544363_66541713_E099839B_1F845B10_9151E645_A4152E39,
    256'h38058FE4_D87EFE8A_EC6525DE_7A53057D_B799DDD1_D1CE8EDF_344C07BC_C5A114CF,
    256'h0895BAC8_3B06DB86_8A865CE5_716D842E_29498A9B_10A5A0F0_82616D4B_5DC476A4,
    256'hAB251456_4637BCEB_8102C85A_DD7AAC46_3DBD3369_D9B92E7F_A55A4921_551FFAD1,
    256'h3D706523_D1E31E23_323A19A8_AC5A7D8A_40EC254E_06B6C174_C823A214_6339983A,
    256'hAAA83615_5497245C_E5920735_3CF51326_91581A9D_80C594A9_9A87725C_43702304,
    256'hD6AEBED3_85B67193_F1184C3A_5068DC16_EB772D14_7E7220CB_4A5ED901_0BD2AE37
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h3276E7C6_778216CD_53E2E587_93A9A00E_2B2293DD
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h59E194DD_143B9424_F38CE83D_5C589C9C,
    256'hFDB07476_AF86898B_0446D8AE_E2BC57A0_0C7F4D48_0EAB24FB_1A49B4D6_72FF94B8
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hD2696788_A8735B27_982F5007_A24A125F_876C9CA6_DDEB52AC_92F5600D_2A41BC46
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h5EFE57AA_3B59BD6B_0A402163_63420F04
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h1ED29A96_5B68FAEA
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h3E59D4F2_E2A0B42E
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h09CE4760_A94FEDAC_F600C64D_0FDE2259,
    256'hF906FE68_05A52D63_EB4568B7_1F115D0D_C48494EF_04EB27CA_B2DB7547_88FB0AAE
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h95A6C4FF_0F42EF01_F3D4575B_AC9CB509_04E880DB
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hBE6E65C3_59480858_C39611E6_58C97FB8_D3E9CC0E_7F8FA872_5200C726_C8F90EF5
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hE2B74BEE_E27CFA19_EA576CA8_A8225C8E_17053E44_B68DD782_2A6859F2_CF52A55F
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hD181B082_D03C5837_56F11AA5_B37F9544_C4AA90EB_97E1C0F8_086F627A_281C5681
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hD6566641_EECCCC88_876AD113_C50AD1BE_4D94DCE8_FCA54128_A3860AE1_D3493FBE
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hF6B9BA5D_FE4463A4_615EF467_62A794A8_C2597E69_FB259B96_1914CD75_BBFD36BA
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h48E780D2_7CD58254_0C7A68FF_254EDFD8_52829FEC_CCABD4AF_9C9032DA_20BDAF59
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hFE2AE209_B8325D2C_8C35FC96_0679B106_A87E59E6_AEB1B530_2D334010_70251696
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hFBB4BA16_9A6CD82F_AD46A0A5_C04009BB_934C7EF7_B83B6E40_610B4309_FCB9DC54
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hD4276137_F9901D09_A76AEAA1_9DE5C579_FD38BDF3_8F0C21D6_A52226B6_A4A7BDB0
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h5FE92161_5BF2FF98_4540F7D4_3ECE76B4_EB133637_74ED2ED4_5545E927_F6D9E4AB
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hAC398D42_C745EEF6_46C1464D_CA86DAFD_7C7C71E6_058DDFD8_71C51CAC_BAF4410F
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h06DCC036_FCD16FCD_E97D1718_91105DD8,
    256'h95E3A1D0_A19A16D6_DBD8B20F_C9E662E1_E1B4982B_3E8EFF63_890DBEAE_926FD468
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hA77EFDE3_DE5B4CAF_4776A247_BABA4C99,
    256'h08ED16BC_5415EC16_D28C5355_1312FCED_CF2832A6_6CEACF8E_D4D5B616_177DD43B
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h56FA754E_1F53AD65_8193B563_D9BDC6D2
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hAEE84852_F0CC7371_ED3A6FAA_516C144B
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h34C96DFA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h60FE0321_49A57A1C_1C56DEA7_0C965C5B_A247F9B7
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h1A643511_8B5F5F3F
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hD3B93131_16B67192_D856DD74_2D40E072
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hE417AD9A
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h7443A428_FE2DE15C_7D33B199_C90DFDA3_7790088B
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hDC260A79_998EFF5C_710B6783_8ADFB99A
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h5ECA6716_72CF19BC
  };

endpackage : top_earlgrey_rnd_cnst_pkg
