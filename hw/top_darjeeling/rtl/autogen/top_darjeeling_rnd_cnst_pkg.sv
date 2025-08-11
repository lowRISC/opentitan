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
    40'h27_2EFAA51F
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h34F8_105CA313_78705D70_B6420112_544A28D5_6256A659_B9C63A11_487E4103
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h55176264_E55C329C_8AE4725A_EAF67281_50127AC7_55D70063_277642B5_309A1639
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h90B966CD_494444C3_BCDF8087_B7FACD65
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hE9654CD8_5BC66D10_208C4FB5_1B97BBF4
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hD12C378C_CFD6A5A5_BF3032DB_51FA1EB9
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h2F6CE10E_90F9C5C0_6F733DC9_11A321DD
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h4C0AC240_6D467215_DAB3F2B5_4A52E672
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h8678AF07_18068E34_4D2EAE4D_73C8FA54_DE8AA4A4_F258F3B2_A145FD19_50AE55D6,
    256'h93E57968_117E66DC_634155E0_F8150242_862EB20E_EA9A1F75_44716551_512A112D,
    256'hED678CE8_24A08E29_C772795A_358EC30F_1BEDD1AF_0EC9D9A9_CF36A2B1_30D32AFE,
    256'h121AF734_F628363A_AA0E93D4_5C423690_ED05BD1E_710F22D1_095889FB_D8A7B57F
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hB1E11DF3
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h47C16293_507A44A9_6F3499CC_30DFB573_62BE7B0C
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hA1DCD048_88055411_66F1EC8C_EB42692B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h089A6F99_B1A7AC08_4224ADE4_612980D4
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h8E6C6493_A50EEDBA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'h02566EB2_13C537DE_7BA1307F_72BC145A,
    256'hAD3533AD_9F0FE248_2B8C8475_86C256D5_C7BE0406_DF33A345_29E4F0B9_A279AA71
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h14A8F2B7_5C265C9C
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h47641A7F_ECA51196_FA883269_7778EDAC,
    256'h7E2F6352_0D2A7594_CCC9803C_E5EE5747_82170EFD_E6890B80_6053AA17_12C7CFEC
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h5BB39D12_2EB54831_88E73FFC_AB0C770B,
    256'h27D584D6_17DACA59_6D07242A_668132E9_742C5FB8_3C952F4D_11E0B63A_2B9DE03D
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hA0D95CE4,
    256'hEE55B032_C07A29B9_20B7953E_485F23AD_102C6A0E_FCE9F0EC_4C712146_A4AB60DA
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h646B7344_050D0C61_01416F8A_7568107E_583E351A_0F85628E_495C3806_999C7629,
    256'h27579591_88225470_601D6948_1E71312C_13439F6A_4E84041C_460A3498_23256787,
    256'h8C5F9672_86092D55_4A4D4B63_325E5302_8F1B3A90_21421880_2033503F_79082F7A,
    256'h7B813978_0B281536_4C036D7D_07169493_66374F24_405B1F30_2A0E9247_6C7F749A,
    256'h2B3D5D14_56774500_8D269752_2E115112_5A3C1789_833B9E59_827C199B_9D6E658B
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h382AF33B,
    256'h47971855_8E675976_4645AAD1_FB21C181_24635E3D_50A88F68_08045627_AC18F377
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h6C6518BA_9E6496C2,
    256'h467B4906_91117EA9_C32B50EC_6EA3D286_3650D4B2_DADD0A95_EC16C7C4_D0930647,
    256'h6A86481C_677D1E2B_2C5F6788_DC5C4026_0B338459_AC581882_F64A1000_51556326,
    256'h4ADE7F9E_AF134199_4B1B6640_7C2E6668_32907D97_805AAB2C_6A570A4B_1C9195E8,
    256'hAD8C89C2_21F9746E_80B5E550_025884E7_265A1A55_2F8B6263_B9959302_70349445,
    256'h47F72A41_3C60A840_F0B3C0B9_18D1B910_DA91FC4A_F0B5F26F_C0A29851_7128A8EB,
    256'h9B120257_0821D349_DEDBB53A_A3EE9901_23280D72_2CFF0E46_63CC752F_D4D0AEEF,
    256'h0E1C330C_C60546C5_BE7D781B_B41A3C3B_5975F5CF_C11C5061_DF4944E4_C7075AA3,
    256'hA46AF23E_6A197C9E_5D2C3C22_56232E31_4A170480_62558858_4D21E4F7_210C532D,
    256'hA0BE04B8_49A74140_AA29D814_679460BA_A0820078_5779E497_4A8C2ED6_868DC665,
    256'h8E926CAA_04602370_505AE437_31B47403_FB6C680F_A6D6AC33_0B8C9404_C853A27B,
    256'h70DD6C08_17C6B562_CBE2D59B_8A86A871_A6B6A34B_DE70268D_A1EAE067_4F697434,
    256'h1D885670_6DA45646_01FD560D_B4828B4D_CE4894EF_3CA00039_E8180002_BE8129E2,
    256'h338B100C_15644061_972A6845_BCB22684_D2E5359D_646D635E_D9A3015D_AC11DC1A,
    256'h387C31BA_E5754FE4_26E6E241_2DE471CD_860089AC_B73A0481_8A1B2B1D_90BE8459,
    256'hC6558977_0DC6B4D8_24626D29_DF03C61C_89951229_8861C4FB_64D4779A_3E3F0E3A,
    256'h2628136F_3106A3AE_0FAA0E99_824B098C_A423E96B_004F889D_5430D55A_5ECC06CE,
    256'h229EE72C_28B84139_F80F7ADA_CA615721_CC45DA01_C00A36B6_9C3FABE9_65D48B31,
    256'h9B9E6C69_62F6C892_54273328_55438474_894ABC2B_DBEAF987_5118C52D_80D60AF0,
    256'h9FAB0D86_BD5CB18E_0C70D330_92A6FED5_9F0581F9_C74E480A_E8AE0058_2B36AF78,
    256'h64412AA8_2F0CC0C6_CA1F6744_CE1E0744_976C5E6A_1457270D_63A0E07D_F70A5FAB,
    256'h32C9294E_6619796C_E5EBFCDE_AB5E41EE_7594090C_7E353F6F_542239B6_293C46F4,
    256'h75E58084_96C76BB9_82855BB0_937DFB7D_61A50835_52129AA6_9A82C034_F04631D4,
    256'h4815BE42_99424C19_42D4C351_AE4ECB2A_00022A20_FBBAFD22_6619E126_5989D5FC,
    256'hF8C39B56_346E041F_20F507AF_D0FB4E87_892D7569_510D8D99_505C4F82_660DF8C2,
    256'hAFB9170F_645A4152_D0938058_FE4D87EE_A8AEB352_5DE7A530_57DB799D_DD1D1CE8,
    256'hEDF3C500_7B7C5AC5_4CF0895B_A803B06D_B868A865_CE5716F0_C2E29498_B1E10A5A,
    256'h0F082616_C1B11C47_6A4AAD91_4564637B_CEB8102C_85AB27A9_8F6F4CDA_766E4B9F,
    256'hE9569248_5547FEB4_4F5C1948_F478C788_CC8E866A_2B169F62_903B0953_818174C8,
    256'h23A21463_39983AAA_A8361554_97245CE5_9207353C_F5132691_581A9D80_C594A99A,
    256'h87725F16_702304D6_AE4E16D9_C64FBF21_30E941A3_6EB772D1_47E7220C_B4A5ED90,
    256'h10BDC6A3_745AEC61_01C14D1E_4099FBF9_8744C451_0DA91C05_D2AED696_E53A6C6F
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h8ECED885,
    256'h9F464D1D_910540EE_C6BA0486_F07CFFAF_7B8B9213_BD8DC7B9_27797C09_DFEAF127,
    256'h2B92ABC4_09056CFA_513AED0D_E2186C2B_2A4874E4_ADACA4C6_809E571B_351756BF,
    256'h8D18E24B_E7E1C967_37B726A4_C6F04993_B3E6AAE7_0F22AAF7_48B57C32_0264E157
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h52DD59F5_60E06B6F_A776C089_70B3A9FC,
    256'hD8B996F7_FAAFB874_4C58C7DE_EF28991C_A47B01B3_3D022A55_70446D83_00292C78
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h600D2A41_BC465EFE_57AA3B59_BD6B0A40_21636342_0F041ED2_9A965B68_FAEA3E59
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hD4F2E2A0_B42EB9A8_C3AB227B_50766D2E
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hAEC89EB1_3B07E9BF
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h4EE42784_136D42C8
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h73A93266_A6B6E1FB_1DCE0B54_C02F3E00,
    256'h63EB8BD5_858F5418_A040791C_3C694CD4_8C9CA20B_DE5EEF7A_6BA157FD_0939B457
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h474D410E_D8502FBD_47E50A56_C6E64724_E0FE3BD5
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hF90EF5E2_B74BEEE2_7CFA19EA_576CA8A8_225C8E17_053E44B6_8DD7822A_6859F2CF
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h52A55FD1_81B082D0_3C583756_F11AA5B3_7F9544C4_AA90EB97_E1C0F808_6F627A28
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h1C5681D6_566641EE_CCCC8887_6AD113C5_0AD1BE4D_94DCE8FC_A54128A3_860AE1D3
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h493FBEF6_B9BA5DFE_4463A461_5EF46762_A794A8C2_597E69FB_259B9619_14CD75BB
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hFD36BA48_E780D27C_D582540C_7A68FF25_4EDFD852_829FECCC_ABD4AF9C_9032DA20
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hBDAF59FE_2AE209B8_325D2C8C_35FC9606_79B106A8_7E59E6AE_B1B5302D_33401070
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h251696FB_B4BA169A_6CD82FAD_46A0A5C0_4009BB93_4C7EF7B8_3B6E4061_0B4309FC
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hB9DC54D4_276137F9_901D09A7_6AEAA19D,
    256'hE5C579FD_38BDF38F_0C21D6A5_2226B6A4_A7BDB05F_E921615B_F2FF9845_40F7D43E
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hCE76B4EB_13363774_ED2ED455_45E927F6,
    256'hD9E4ABAC_398D42C7_45EEF646_C1464DCA_86DAFD7C_7C71E605_8DDFD871_C51CACBA
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hF4410F06_DCC036FC_D16FCDE9_7D171891
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h105DD895_E3A1D0A1_9A16D6DB_D8B20FC9
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hE662E1E1_B4982B3E
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h05700CEF_8725C61B_0B488D10_7BC24E80,
    256'h73FEAB3D_AD64DE46_2BD12E53_F9F75450_A6CB0A1D_47A4D67E_96B56E4A_EF0E2623
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hAA516C14_4B34C96D_FABB6F6E_79208A74
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hF35C79F3_97C4E4C7_E22B7581_848A90A1
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'h254B2276_BEC9FC1A
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h638051F4_A7E18333_ACD09FC7_EA96B70E,
    256'hB6D4C350_02BE3E65_A2740B77_E91C17BD_8FB57884_3591969B_1312B93C_BCA8855E
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hDC260A79_998EFF5C
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h710B6783_8ADFB99A_5ECA6716_72CF19BC
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'hA6ADC1EB_FAB611F1
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h9E7262E0_A491970E_51B28E70_26D0E5DC
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hE9E265A4
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h32B4FA62_3C5A2F69_14E90832_D6767BF4_1C327EA2
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h0FFAFF97_60F5E838_BD8E2413_AB956B10
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h6CA7139A_07EFFEE4
  };

endpackage : top_darjeeling_rnd_cnst_pkg
