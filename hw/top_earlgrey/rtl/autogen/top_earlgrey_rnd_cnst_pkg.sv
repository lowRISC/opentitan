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
    40'hF4_5DEF7861
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h5D29_4061E29A_7C404F45_93035A19_097666E3_70720641_53623855_022D39E0
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h6FAF88F2_2BCCD612_D1C09F5C_02B2C8D1_FDB92558_E2D9C5D2_44407223_25A93144
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h79EE911C_E801484B_A8373086_F9DD4EEE
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h03A0B091_DC41D062_DD10CA2D_7B93136F
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h0EE2A465_FD4DABCB_D877AFB6_BCFEED7E
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h699679ED_D5369F11_B49BAC91_98BD1FF3_44C5DA22_42D290BE_DE094CA8_F1435F85,
    256'hE0F7489A_309CBE57_B77F07FF_3D729720_0D5AB255_61AF49C6_96466A98_3E534682,
    256'h6A436282_19E5A913_89B9FE0D_3B818E46_CE7D8464_69A3B8E3_5A6BD382_95BD2FB3,
    256'h66B3D621_26C75EEA_EB93D32F_5CBC7746_3C919175_16D51A2F_A4400ADC_2669E253
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hE10023EC
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h74449A37_4B5678FF_C0A1C18F_B47BB504_86CB4EE4
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h3635D1F4_7C8F05AF_FC85F7D8_89ECD94B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hC87B6911_1A24D5E4_442BCFB7_032949CC
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h48BAE844
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h46B0E5D9_F9E80FCF_3212FC76_A2B6A11D_2F332482
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h0AF06B42_350BB6B6_8440934D_CB834F93
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hED204633_871CB178_192AADBB_7C918ACB
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h33A4AC96
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h3480D189_6C7FF9ED_5941BD12_5C6EB187_72E220F3
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h8E18EDEB_46B20763
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h05CF6536_A2EE3E49_D22A36FA_59EA2C46,
    256'h20D062F6_9F5F3209_DC203EE4_C87FF199_B2AF013B_1ED4E039_5175C5DD_94E29D06
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h57EC2E41_6728B1FD_9D00A60C_08D538DE,
    256'h2C75CC32_5A65E95B_98BAC182_F10EEB4E_52F2A93D_22D3F24C_51D1A7F1_A387B5E7
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h5147F1EF_84F4B3A9_D281437D_77F97002_2C91C1A2
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h8A88993A_82401112_1A5E9A49_36802793_375F2E64_0110219E_6607524D_79684743,
    256'h5A3B257F_67298E72_469C2395_06756B61_4869422C_91506A7B_76733D60_32714113,
    256'h2439704A_0B908B28_977C4B14_55841C89_56965309_5D3E0E2F_1D150D1F_8F511792,
    256'h048D4E3F_9F1B8374_2B629877_0C26226E_450F6D35_6F4F581E_7E784C6C_57187A5B,
    256'h86943300_030A445C_2A65597D_81871902_3C8C1630_639B2D31_209D3405_08548538
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h30D16A94,
    256'h098E6812_52F1C774_1DD6E621_90D79F12_30D02F64_3AC42FA7_0CB94215_5264F8C1,
    256'h21B7387A_0A07DB44_FE8C330C_A072829F_9970F910_74501568_220E25BA_7743095F,
    256'h2C1194FB_74487A86_B6FEE031_1AF608B7_123F603C_251A36AB_2E658548_C5420BE5
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h65820176_3C640FA7,
    256'h703F4EAD_00959A71_96BABDA7_14F0E5B9_47B3F17A_491F6755_52019F63_1CD435D1,
    256'h8EC12034_4AB92EF3_3C052BE5_A689E5B1_2943BDBB_9CA066D6_D757ED3A_1C50C78E,
    256'h6A158681_4D32D232_97AC79FA_7DA1A756_B9D93EE4_91E66935_A115CA0A_38A63A9E,
    256'hC055AE11_14355A6C_A0B9AD9D_9EBB3877_5157D5F0_707DEBE1_CE7A5EED_58E8F085,
    256'hA8877C7C_9BB1BA96_2E7609A2_7C1C1509_C8E2E871_0FD390B2_B20C5A3D_22AB2C68,
    256'hD084AE82_4860E09D_1E73A88E_14446552_5B74CD40_0D741609_D7E81491_D7771CC3,
    256'hA2662384_0044AC34_CAB15FF1_A9070B1D_AFF72EB7_2B593004_696118F3_2CF70205,
    256'h95FADF87_1F06CAB5_4C652638_FE77A42A_0A678214_BC31E934_87E78148_16E786B0,
    256'h403761E4_515C09A1_A6984C43_ADA03907_2A887432_B03F03B2_959BBF30_15D9A91B,
    256'hAD428CD5_1AA2DB15_3E0C64B8_05F47292_3A6256C4_661A86E3_1091B20A_3F02A2B4,
    256'hB567319E_D19DA1A8_0A157581_8503042A_25281603_22E224A9_C36926AD_2A66E157,
    256'h074D0334_8C329E23_A1BF8922_3799E181_CEE3C8A2_80CE538C_1FAE45C8_BDAF0D94,
    256'hC944B09F_18BC2942_602A94C2_F70560BB_B998C4D8_72296249_D655E9E3_8B0524A0,
    256'hC92EA933_C7066653_30CCBC0F_2B34E5BC_8A04F064_13A3949C_48AEA8D2_9B9DBA64,
    256'h4DC2DE9B_966D8534_28A059E1_B6CB5BE6_B8859265_1B7960C0_29240012_453B52EB,
    256'h35FB446E_B621FFAE_2F6A4513_C261B8C5_D658E661_A027B6D8_D36E2241_96A95696,
    256'h8F4F6974_0CB7166B_C26C2B07_FB58727F_23731E9E_45474940_484F1EC1_06203E42,
    256'hA7159524_27F3B12C_76B1F26E_71A75DB0_DE90AB6D_E5C1C93E_299AC919_8F90BBB1,
    256'h2505C436_8C4E3A54_E247051D_71DBB46F_12D4F299_F37BF1C6_E5821803_DB096DC1,
    256'hDCE65DC1_17D09A2E_C13CDF85_CE8C4A86_38102C85_66DC6494_C0E00B32_9789D348,
    256'hE5DD9500_65B14A47_A640BF15_7A900365_E8545F5B_A8556A26_87E68A01_DC3AF226,
    256'h39CF5088_A7B750F7_0AC96157_1671242D_4617C6FD_40541702_7B305464_DDB18491,
    256'h62C6336C_E192246B_732FA50C_71BA5A0B_96F346AB_DC00B68D_95A2E508_6F4C224C,
    256'h0F259640_F9833388_106E6F21_44957918_1EC57741_35B80A82_F64D56E4_492ABBA7,
    256'hC9906078_836F4791_F6839595_4DEEAA09_86D03A4A_D797C886_35C6587D_C84FD030,
    256'hE02BC124_3BC44D2E_E5775253_2225FA92_FB3D1B08_4DAAC5AB_62FD3B8C_0324DA48,
    256'h37E839CE_F5A36778_3229C204_72E11C2A_502256D2_3FC10AFC_345D6790_85BE4F5A,
    256'hB2782362_5783AD17_2FAAE5A3_0F73C6C4_7550B986_6C088369_510971FD_0A71407A,
    256'h95330027_5CB3BCAA_216AABBF_A8425E4F_A69B6234_64025059_3310178D_E02E4E83,
    256'hCAB4102D_919404E2_104BC7D5_620962A6_59820215_9D5BE011_7F9D223D_61360D1C,
    256'h627018A3_5A008B48_61D0E617_8AAF9110_7A482D10_6952312D_96930D9A_816AA944
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'hD91D738A_787AFFA4_24A1E487_58D9AAEE_61E3028C
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h7D283F11_8981787A_4631DCC3_5E5A0854,
    256'h9E0FEB5A_C58D4464_0936BCCB_BD10016C_2F85BA99_8AC3ADD9_CFA7F6ED_CD2F1E4A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hB1AC8EA0_520D1E94_2E682025_65535CF3_57B4544C_ECD50B63_D8A07751_7EA4B4EE
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h4F2F4EB6_6E1C1664_6A7BD56D_29AC43EC
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h0BEC2924_8EAED09A
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h61480D9E_25EE5C4F
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hB3E8EFD6_42C5BB87_B4DC3557_CFC33198,
    256'h196AC1B5_13E8FC9D_FFD8A069_1D9F64D8_47710ED2_E6D9D608_824438AA_29180AD8
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hE48303CE_FE06DBF1_99D1622B_AC649648_9F42AD5D
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hB46FC99A_E645F3DD_8F3EAD31_DF20485C_EC3B1975_D7E78D34_474B8A3E_1EBD40F2
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h81F213FA_F8A2D8E2_7D0E00D2_BFF0AC38_0A5BDE7E_8AB3461A_9B868238_18D0FFD7
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h66C33522_317DB491_0816E9F3_5A99F403_273CDFF3_AD3389C1_708A2A7A_6DA271BF
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA2CB8F24_F7E8BB0A_0439B0CD_362939BB_2E0D30A4_9D0522E9_A5B96197_D6349A22
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h203BEB21_B48E13B1_27FA42A1_4CEB82B6_610A5457_BBF1CAF5_07098F70_22B6F355
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h0C00998F_E5D2429B_122499F3_98D73409_C6CE2E8C_4CC7AB13_C648D6F3_AEAC01E3
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h25552FD1_10DE6F18_5A80F3AE_276DB241_6FC002D0_4B77C626_E56477E3_DB8EC31E
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h28F49681_9267FC87_61BE9C1A_B36495FD_7C0CB3AB_FF6A4FC7_F10263B0_8FF69923
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hF5D3781C_DC459FE1_C6AC6343_A98F8F32_E989297C_02610693_700D68B4_716EB94C
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h3EAC9951_5E95F75B_2F747AB4_FD7B6483_4768D0B0_CD8A5828_BBF2CD4B_AE6862F2
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h011D8AD4_C0195D90_AE1582AD_51E12EB5_25C2E74D_E16A9346_81A42F3C_72492F96
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h8C974099_F25B8179_0BAF3122_8FC01CBC,
    256'h67C9EA62_ADD8EF45_0563C451_44EDF3C3_312B7EB8_8E6B5C61_4553E6A2_85EEB801
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hF5347613_C1C980F2_B67A2495_92B3504A,
    256'hEEA24843_9F4703D6_03124E32_11B0D83A_2CE3940F_256B3DB0_EB494EE8_937D08C0
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hAFBF21AB_369D0ABF_6E68B959_301E3403
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h1BE8EECE_2EA06860_734991CF_2141384F
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hFFA4CB6F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'hABC416CF_965E23AF_E646BBA9_021CA0F2_91B627A3
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h5360CDF7_14F75BAE
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h96990EB0_46B67B2C_BB2A1859_C5C6A54A
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h26E4D620
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hBF5CDB4B_6620AB41_B0B0E290_08CF4BF0_70979FF9
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hCF829F05_B62E1FF4_CF4A3579_4396ADFC
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h67843D1F_B59AD3D2
  };

endpackage : top_earlgrey_rnd_cnst_pkg
