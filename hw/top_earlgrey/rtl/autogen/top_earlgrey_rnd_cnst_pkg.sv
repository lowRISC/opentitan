// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/
//
// File is generated based on the following seed configuration:
//   hw/top_earlgrey/data/top_earlgrey_seed.dev.hjson


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h30_9A163990
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h28C1_C838F5E3_01069D05_379551C1_8598359F_90408D60_B6C98A78_60951499
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h21DD4C0A_C2406D46_7215DAB3_F2B54A52_E6728678_AF071806_8E344D2E_AE4D73C8
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hFA54DE8A_A4A4F258_F3B2A145_FD1950AE
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h55D693E5_7968117E_66DC6341_55E0F815
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h0242862E_B20EEA9A_1F754471_6551512A
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h112DED67_8CE824A0_8E29C772_795A358E
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hC30F1BED_D1AF0EC9_D9A9CF36_A2B130D3
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h2AFE121A_F734F628_363AAA0E_93D45C42_3690ED05_BD1E710F_22D10958_89FBD8A7,
    256'hB57FB1E1_1DF367C1_C1EDE3F3_5CFC8F6E_72ABDD73_A9EEFBF8_B7081EB9_F636E13C,
    256'hA9D21F1E_DEBE60A2_2DB6D398_D4A21B73_699E8082_0434A1DC_D0488805_541166F1,
    256'hEC8CEB42_692B089A_6F99B1A7_AC084224_ADE46129_80D48E6C_6493A50E_EDBAC6A4
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h6B7A8A9B
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h1119AA85_6EBB4C0F_2B7FB521_91F3078A_133975E5
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h521D4711_E6406690_8ADFD591_8F8C563C
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h92184F1C_76A61E11_2578BF9F_469FC482
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'hFA14A8F2_B75C265C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'hE758C46B_DDBBFD06_1F0C9C91_762BB71F,
    256'h420D2A6A_54AD959B_32500F39_7B55CDE0_85BFAC38_A242E018_14EA85C4_B1F3EB27
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hF6037B9D_ACA18EB5_801C444E_BC53EC27
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hF13EB602_172C4D95_0331BEBA_D605BB69
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h6BE7A52B_9A29E3C8_71EE416D_C904583D_F8BAE9C4_6DEE80A8_69A1CE14_C113994C,
    256'hF87EDA86_140651AC_88EB62E8_34AA3425_C620C68C_E20120A0_D95CE4EE_55B032C0
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h7A29B920
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h076F3C6F_C3CD20A7_9A3F6234_EE05A515_48B49E56
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h3BEAFE83_89E9F8AC
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h73039AA6_E7C86E04_990ABA3E_A860739D,
    256'h8353C50C_87863783_D2230AF1_7DBF55D9_91D40DC9_938EF92E_C97AF541_163EFB45
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h3DBB3322_BB83FE5E_2253DC86_78E62045,
    256'h268B14A0_294DC0A3_116D2692_A9F9EF15_ED04935D_FB0DFA87_532FD954_19A1FF07
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h8A468D23,
    256'hEECBD09D_E6B8F9FA_EAF1A70E_57E8EDA0_3A353B76_A2F83350_9ACC7B3A_A3FA7DAC
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h111E1D25_77374387_2E29390F_513A9101_12627B52_4E484F7A_706E8D5B_69736F68,
    256'h57072D09_827C2C71_3C801B7F_4C969098_79323F1C_2766846D_9E858640_9C314449,
    256'h28422697_617D4D10_8B955C9A_928A176B_58835D14_5F05740A_889B4120_65728C99,
    256'h22896460_08333519_0E2F0B75_157E5A1A_4B93530D_036C8F0C_56139D02_04348E54,
    256'h503D9463_24812145_46765967_5518473B_2A38004A_5E16361F_6A30069F_782B3E23
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hE6AEF30D,
    256'h8577834C_CC6CAAA6_3A8E6604_338151B9_A23C08F9_EED04CA1_EBB0BDD3_05FFB6C4
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h8B5F6C52_E176ECC9,
    256'h267E5E0B_16556F95_8B358087_6599D178_E1BB8D00_E2FD8DB1_C756ADAC_F0A2671A,
    256'h1A247312_D321189B_52E29D47_7782D15D_6295A4A0_4D428C06_8711DA64_3416B6E8,
    256'hAB69C55F_555BAA79_BE17C0C6_6F3D57E8_0A25A3D8_BB807D46_52D1331D_229686E4,
    256'h1E231408_86D9AE88_852E0771_EC0A4523_52814718_722AC326_328274A0_0C20BF53,
    256'hA4215459_125DF3B4_5273D4DA_C4333712_71CC2582_2F57A30E_349B0C5E_FE15F0F7,
    256'h59D03E5F_134DB6B2_03A994CB_28A0C8DE_FC3FC092_78FE09C8_D6FD0E55_92F402C7,
    256'h318C17AE_9EBE9F99_AA7D5D92_C78A9041_A8B771D9_8E67F94F_061A6E56_F0C3AE12,
    256'h29CE8E93_DD313E9C_139AC03D_ECBD26DB_611F97AC_38D6845C_47FB199E_4C4D8982,
    256'h26068200_54CA61C2_D5E88019_04AB9D63_415933DE_782EA0E5_186C5AEF_957840A2,
    256'h4E92F60D_871D1309_1A604AD6_09C31442_A12CC524_6961E498_1F2E497E_A40FD090,
    256'hACAE852A_1AA012C6_71E2489C_5DD45946_03B5C0D1_7E3235E2_C11011C2_7123B818,
    256'h26DE5844_67560562_0F11721E_6C36ECC5_A2AB58EC_455AD3C6_99C2F150_180C4AEE,
    256'h93CD525C_9BB28EB9_2E6DCA0C_8B0F8A1B_AE011F8D_119A1732_630321AF_681B496C,
    256'hDDAD5745_0C813330_4ACA882F_8B5462F3_3566B1AA_5D7C2BF6_C97B8255_7268DA4A,
    256'h1251E9BA_82A503DA_130D0762_15D41B6C_F9A1EE57_19A66CDB_4813AB55_6C648E44,
    256'hDD33998E_F8C4F24A_80E00460_000AFAB0_A7990E29_85020C1C_A4406188_AA04E413,
    256'hA5EFFAB9_C94D1978_40D69011_B735E76A_D90430C0_6A1C2B8D_1D011FC9_EE3D33B0,
    256'hC7862759_285175A5_53D0445E_4C471119_64086029_AB296A07_4B73A1CB_1221B970,
    256'hAC3802FB_35671956_2BC43787_9366A424_91132A98_B41C150A_AD122988_6761A31C,
    256'h4FB29218_0723C8BE_F038ED29_A5ED6844_D90C41AD_99C92307_7D1CC586_71ADC9F1,
    256'h0E286AA2_EA327425_40A140E7_ABE418D2_152DB186_202E51DF_D8FA382E_E701AD24,
    256'hBA0AA874_8F1D40B8_8D3F6C57_07028D69_E462C0FC_4055D962_BB160949_2D99188F,
    256'h03EADDA0_4BC0E58E_BC81F7DC_297EB1BB_BCA5880E_6619796C_EA305CDE_84AFB790,
    256'h7BAF6952_406F9DCF_D5B5089F_0EAB7D9F_4E1D7BD8_2125A98B_7AA5B396_E9E8DF7E,
    256'hDF586942_0D5488E9_29BDEE68_2C034F27_2118C751_2056F90A_65093065_0B530D46,
    256'hBA764ECB_2B24022A_20F25CA9_226A7B05_26A01662_757F3E05_36D58D1B_8107C83D,
    256'h41F0343C_23B42249_8D985695_10D8D995_05C4F826_60E939B1_F8459419_151E645A,
    256'h41531F93_8058FE4D_AAA1F596_2BC09497_79E94C15_F6DE6777_47473A3B_7CD1301C,
    256'hE5B2C5AA_F845AA4C_F0895BBB_43B06DB8_68A865CE_5716D842_E2B0A526_2A6C4296,
    256'h83C20985_C4313AF1_C476A4AC_15145646_37BCEB81_02C85B00_7AAC463D_BD3369D9,
    256'hB92E7FA5_5A492155_1FFAD13D_706523D1_E31E2332_3A19A8AC_5A7D8A40_EC254E06
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h3B07E9BF,
    256'h4EE42784_136D42C8_5E456F3B_26D15F55_84BB9879_BD249785_2C23D0FA_289C3348,
    256'hCE364ED5_34970E1F_D45EC606_BE134FC0_8318BD29_B22B08DF_647BDC30_068E7513,
    256'h200FA828_BFEE3ECC_F02417FA_68D00453_4267F60B_34A8F072_E77EE485_9B243F92
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h4DDACC9D_AFFECA10_4F3BAF62_617A4A90,
    256'hD1507B18_07A3644B_23B546B7_7F090147_2A8F40EE_7F5125E7_80925B06_5BBE6B33
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h627A281C_5681D656_6641EECC_CC88876A_D113C50A_D1BE4D94_DCE8FCA5_4128A386
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h0AE1D349_3FBEF6B9_BA5DFE44_63A4615E
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hF46762A7_94A8C259
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h7E69FB25_9B961914
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h661C843B_BA36FA2F_30BC1407_8E6B45C5,
    256'h8B1BFDC9_4F03A191_2D7A4229_620C92BA_A7DD44C9_69E0D5E3_57F48394_BD36E773
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h165CB816_B3C6A20E_6C6622A9_6F33ED3F_5E995C28
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hA52226B6_A4A7BDB0_5FE92161_5BF2FF98_4540F7D4_3ECE76B4_EB133637_74ED2ED4
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h5545E927_F6D9E4AB_AC398D42_C745EEF6_46C1464D_CA86DAFD_7C7C71E6_058DDFD8
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h71C51CAC_BAF4410F_06DCC036_FCD16FCD_E97D1718_91105DD8_95E3A1D0_A19A16D6
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hDBD8B20F_C9E662E1_E1B4982B_3E8EFF63_890DBEAE_926FD468_A77EFDE3_DE5B4CAF
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h4776A247_BABA4C99_08ED16BC_5415EC16_D28C5355_1312FCED_CF2832A6_6CEACF8E
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hD4D5B616_177DD43B_56FA754E_1F53AD65_8193B563_D9BDC6D2_AEE84852_F0CC7371
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hED3A6FAA_516C144B_34C96DFA_BB6F6E79_208A74F3_5C79F397_C4E4C7E2_2B758184
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h8A90A125_4B2276BE_C9FC1A7A_5722A9AA_CA4DB84A_32E5C698_5A1A6435_118B5F5F
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h3FD3B931_3116B671_92D856DD_742D40E0_72E417AD_9A5F2612_04CBCC69_A2147819
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hB290A4BB_0264347C_0F91B0CE_C93C0129_D85B9580_1DBE03F1_7E69DC26_0A79998E
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hFF5C710B_67838ADF_B99A5ECA_671672CF_19BCA6AD_C1EBFAB6_11F19E72_62E0A491
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h970E51B2_8E7026D0_E5DCE9E2_65A416A8,
    256'h12231CFA_76E3D982_F8FDCEC9_AE1AF0B8_CD9E1760_6EC98106_0E94795A_1D573089
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h578C104A_36A647E9_0FFAFF97_60F5E838,
    256'hBD8E2413_AB956B10_6CA7139A_07EFFEE4_57DEE82B_6E06663C_291739FF_0E7D6447
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h58FEE1C5_8564CF34_6D9622E5_37109136
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h6EFBD61B_0CB470B9_44EF806E_573B44B6
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h43EBF0C5_DE019FC0
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hB99612D2_78F8A975_9DA4322B_F1F55305,
    256'hB821CEF6_80DB5DC7_170B2D94_610B7B2A_0F38A08C_24DEFDE7_AFD04648_949BEC5C
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h356888AE_5343DD78
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h4CBA5BEB_BE2A6EAD_062D9516_FDD8B110
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h861A797C
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hAE8D23A0_970E7624_B55C64DD_D5BFDF1C_70505216
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h1C67F59C_BA5482C1_E35E6E33_35C20CC7
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h78FC3099_17B9C870
  };

endpackage : top_earlgrey_rnd_cnst_pkg
