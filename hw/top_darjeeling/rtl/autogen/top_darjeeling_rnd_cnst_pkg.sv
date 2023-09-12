// Copyright lowRISC contributors.
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
    40'hE3_0FAD54FF
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h2258_669E26E3_80658F61_731F1491_D19022C3_78438D75_92934156_8151C480
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h17B58D85_77A87D8F_67508E57_6E4353EB_B9C76670_9E58B272_14878D6E_689F385B
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hA2ACFE0B_0057F563_F3450B66_AAB3D8EC
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h2E66B6F8_5CE54924_95FB4253_0FCAD915
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h8DC97AD6_0B2FDD23_F3986313_D612FDCD
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h62AFD0C3_A5FC772C_EB91C16F_5D6E17DF_F0661BFB_A6F4E057_1EAE0FC6_E6A1A665,
    256'hF042709B_54CB121F_7002A405_ECDCF1FE_B0FA7A14_877EC886_3787AF27_2EFAA51F,
    256'h0DE710C8_91D47FF7_209F95D6_14848E38_361CD9B7_EB23D532_C0AB44E1_E92CCFEB,
    256'hADAD9193_A3EE4ECD_8C032462_B3E18549_CB1E70D5_A83DE667_3D2C1C0A_7B551762
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h64E55C32
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hA7ED5C94_F7919BE0_A47B4688_C061E254_3AB77233
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hCD65E965_4CD85BC6_6D10208C_4FB51B97
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hBBF4D12C_378CCFD6_A5A5BF30_32DB51FA
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h1EB92F6C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hBE4D0058_6A796AC5_C67BEE91_E492823B_9BFC483C
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h344D2EAE_4D73C8FA
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h6E35D2EA_A4E72723_7D078B48_DA53CEC3,
    256'h9D6F9AE8_02EF128C_73E7470C_B874005C_D06197C4_69E93FAD_4191A2C5_BCA62DD5
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h1987B4B0_B449B523_C4FDD033_DE0F7CA1,
    256'h31543279_70695866_DABBB9C5_B8F86727_E9896088_EDC1EF07_AF905F59_03A8E34A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h9A6F99B1_A7AC0842_24ADE461_2980D48E_6C6493A5
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h35375081_637B5E70_21060D62_3D67573A_51029907_044B8968_8622163F_38154D7F,
    256'h319E854C_931A691C_34655A98_6D00744A_6C322D71_3052118E_14723E28_0B8F9A36,
    256'h1977018D_1D2F582A_40660560_9C244276_17876E03_26554384_2559805D_132E5B54,
    256'h0A90647D_4F5F3C12_7C0F533B_7E270C97_1E8B4696_786A8845_48332073_08239F29,
    256'h4E442B79_94107561_6F095682_5C1F1B83_41189195_398C4749_929D2C9B_8A7A6B0E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h416DC904,
    256'h583DF8BA_E9C46DEE_80A869A1_CE14C113_994CF87E_DA861406_51AC88EB_62E834AA,
    256'h3425C620_C68CE201_20A0D95C_E4EE55B0_32C07A29_B920B795_3E485F23_AD102C6A,
    256'h0EFCE9F0_EC4C7121_46A4AB60_DA8B656E_ABB0B3EF_6E9B197C_E582FC9B_5965D697
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hB6E1CA67_009A2A60,
    256'hA96F146D_C2B4B174_14D0F992_C5C46AAA_A3138D00_28B5235F_C8331509_E361EAC4,
    256'h1414B3B2_96421C80_CC608BD6_EAF6B436_9E6966C7_01818BE8_3FC2B134_96D2B417,
    256'h91D9A895_14732CF9_3847F22D_241A5186_41890254_3B963EC6_1CB375F1_7E6E368C,
    256'h6C406077_D8E4190E_9A28A00A_CF32FA46_5929EBC2_FB4D16C5_79569E1A_15869F6A,
    256'h9D535D23_0D01F9B0_F79C1ED6_C1DF7445_75F20BA0_A8746D40_824166B0_AAC12448,
    256'h48408A9F_7199E24E_9867345F_90CC6232_C2345009_031E6D89_A8865D64_C0E6C92B,
    256'h428C8095_4EB20BF8_94C9349B_9BADE55A_4123D86A_512BCA26_BEB3D772_E87BC71D,
    256'h84B20F3B_E499461B_4C622482_284A1BC9_0A9069AB_33C41E22_081BBD97_456741B4,
    256'h682420A5_AD36840F_0B9C2D0E_1C3379BB_75872B04_9B5D9802_668B7282_E295D205,
    256'h4EDA5067_9998849C_79800956_E9482ECF_F9ECEE0C_90673C00_2BE8329C_96389F50,
    256'hC2E0B2EF_17195569_6263595D_6B602302_14AA59B8_D27E80E3_2412E147_30F932C3,
    256'h6CDD73A1_BE18B0E5_F6E68F06_5C06A81A_C244FD70_A9EB96C5_D4298861_C59EA3E6,
    256'h224CFC38_E41BA429_1066776D_8139B057_86DE9B44_F086F843_0D57322E_7918E860,
    256'h28AE0136_FD8C91E4_EC6C8731_27AA90A3_8830B69E_2C652BAB_52290D49_2541FA15,
    256'h6FD11D22_52A6BB8A_9844529B_A160A4C9_F3615C94_2CD868D3_6AD2A9F6_35161C27,
    256'hB8802BA8_C60AEA98_205129AF_33031A94_7DA6B1F0_75FD1794_5ABCC76D_00F3EEF9,
    256'h5EE84960_C530975C_419A4428_85C62D30_EC5674BC_7A223BB9_9602DEB4_25C7664F,
    256'h29D6082C_D631225F_0DDEC1F8_B6211F4B_D4753721_19149C74_E5E02217_12ED1036,
    256'h9D449953_9CB77C2B_F3F4FA89_D0D2864B_A38A4474_942293C8_924D6710_5589D900,
    256'h49E4E63A_8765C79D_6728AB27_256A37C8_5329A07E_C4962E57_0650B532_DA6B93B2,
    256'hCACA008A_8A569222_63149B16_2757FB56_C06D58D1_B8107C83_D41E6543_E7C8FECE,
    256'h569510D8_D91713E0_9B0C7E2A_DA86B1BD_DA415309_0161FA46_2B991497_79E94C15,
    256'hF6DF111D_1CE8EDF3_AD6ECA18_5AADB060_8AFE9BC3_B06DB868_97316EAE_C34420F0,
    256'h826166EA_71C4B664_A4515918_DEF3AE04_0B2F298D_EA63DBD3_352E7FA5_5485547F,
    256'hD3D70652_3D1E31E2_3323A196_2903BDA0_605D3208_D4633998_B5E0D855_525C9173,
    256'h96481CD4_F3D44C9A_456B4E76_032C9C0E_6A1DC97A_DDC08C13_54E16D9C_64FBCE13,
    256'h0E941A35_DC47E722_0CB4A5C0_4BB6BB8D_F126101C_14EE4409_9F61D131_14436A47,
    256'h0C08AB96_E53A6C6F_B5958082_3DB61782_46AB4656_58E46147_8E09FF14_1647C304,
    256'h1A780F8C_74EA509D_A352800E_67723D1A_87A85A81_C5B31370_BD2F4B44_DB765601,
    256'hCBD04673_AB31A85A_A255D7E5_4D915E81_436EFF43_B1956E81_11238174_A9987073,
    256'h3CB04CE7_9804FE60_CB82B174_149DD45A_C600C985_98B996AF_C5A2F4B7_EB083B08
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h2BBE63CE_991C1F1E_E1225825_A432ED22_B76AF83C
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h7ED0D0B1_48179E63_46A19398_06BC768D,
    256'hE27074FF_C0869D7A_DF21CABB_445512A9_0C59CE3D_BC88B3F2_52C26BEE_7B1526D3
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hDA2D53E7_CA15201A_8F565300_10117F58_C9E9946C_11180407_FEB4710F_404E6E4F
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hACE59B97_2D1FDCAF_711C0569_397BFC41
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h976AC86B_02BF2B89
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hBE218ECE_D8859F46
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hFB57082D_176500F4_9758CEA7_6199A0DE,
    256'h8FFBC1A5_73A6C14D_1833946F_8AB22AD0_B6D09E63_BC4F627A_B7E1F2EC_500641D3
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h7EA93BF6_30AECEE0_C876413C_BC89AC30_0A9C7D5C
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h121F1E16_4EAC2904_2563AE47_33313AD2_696788A8_735B2798_2F5007A2_4A125F87
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h6C9CA6DD_EB52AC92_F5600D2A_41BC465E_FE57AA3B_59BD6B0A_40216363_420F041E
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hD29A965B_68FAEA3E_59D4F2E2_A0B42EB9_A8C3AB22_7B50766D_2EAEC89E_B13B07E9
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hBF4EE427_84136D42_C85E456F_3B26D15F_5584BB98_79BD2497_852C23D0_FA289C33
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h48CE364E_D534970E_1FD45EC6_06BE134F_C08318BD_29B22B08_DF647BDC_30068E75
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h13200FA8_28BFEE3E_CCF02417_FA68D004_534267F6_0B34A8F0_72E77EE4_859B243F
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h92CEB098_BE6E65C3_59480858_C39611E6_58C97FB8_D3E9CC0E_7F8FA872_5200C726
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hC8F90EF5_E2B74BEE_E27CFA19_EA576CA8,
    256'hA8225C8E_17053E44_B68DD782_2A6859F2_CF52A55F_D181B082_D03C5837_56F11AA5
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hB37F9544_C4AA90EB_97E1C0F8_086F627A,
    256'h281C5681_D6566641_EECCCC88_876AD113_C50AD1BE_4D94DCE8_FCA54128_A3860AE1
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD3493FBE_F6B9BA5D_FE4463A4_615EF467
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h62A794A8_C2597E69_FB259B96_1914CD75
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hBBFD36BA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'hB4CE88D2_EC181C59_2C553671_F2376157_7CFD4389
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'h79B106A8_7E59E6AE_B1B5302D_33401070
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h251696FB_B4BA169A_6CD82FAD_46A0A5C0
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h4009BB93
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'hDD053595_D00763CF_FA55B0CD_922B1A0B_10D3DDE9
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hA7BDB05F_E921615B
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'hF2FF9845_40F7D43E_CE76B4EB_13363774
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'hED2ED455_45E927F6
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'hD9E4ABAC_398D42C7_45EEF646_C1464DCA
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h86DAFD7C
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h242D9A30_F392D5A2_ED3717DA_6E85151E_3D1071CF
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hE1B4982B_3E8EFF63_890DBEAE_926FD468
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hA77EFDE3_DE5B4CAF
  };

endpackage : top_darjeeling_rnd_cnst_pkg
