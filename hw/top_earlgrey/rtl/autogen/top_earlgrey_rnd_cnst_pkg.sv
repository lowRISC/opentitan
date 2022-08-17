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

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hAA3CF1C7_FEC9F29F_DE876AA5_8DAB46F4_F7B0CE3C_FFDA0E97_82216C07_46509E39,
    256'hF6D4E529_C9F758F8_73D25A17_251FBE68_478B95E5_38DE6EB3_4DFA33F0_33A4AC96
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h72BB2473
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h660BE981_B6922265_BC8718BF_D76E950F_219D26EA
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h83D6D00B_39FF9E2A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hB0D5E716_06D63DA4_35ED8B83_2DC97CE6,
    256'h9BC87E4C_22A9EE0A_DE8FA307_4C924495_4200EC5D_336846E9_9FF34EBF_44507B66
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hE7B4F223_7D969C25_3D7253D1_1DE43E54,
    256'h524AA980_3F3695E1_AECE19CD_A8BA91DD_1F1B5BC3_6EE9BC2D_2A300608_ED13138C
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hC89A3209_A1642741_192E3979_E50F4B73_02BF908C
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h43834947_91069F29_850F2E96_2B3A3411_209D609A_9E05861A_8F8B529B_125A267A,
    256'h807B2C3F_624C2388_82927821_70389464_69074A42_4B557246_3589255F_7E224F32,
    256'h3010610C_369C7C48_53276F40_583B5008_73132439_846E0B3C_1854288E_6D761497,
    256'h95561C1B_742D6B75_09793E66_0E2F5D1D_67150D1F_6C685E02_77511716_04994E7F,
    256'h71370145_57419319_4D908A1E_6A3D315B_9863338D_00030A8C_445C2A65_597D8187
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h4857FFE3,
    256'h8745AE40_0E4AEE83_85F157B8_8AB8ED1F_CE7408F7_BE58B7D2_1102BE30_1EB1A8D0,
    256'h4814AC33_B45DE425_069E5959_DF06D422_54A25AFA_E52A5963_310FB843_B64EF41E,
    256'h69029587_C377A10C_9AB33F80_F21FAD72_05BE139E_AA9FBE94_51206955_30D16A94
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h9D0807BD_69BCEB5B,
    256'hB8319ED2_33C15C98_6E6B558B_89073142_F46F0FEA_958FBEEB_F575EB0F_DDE1C054,
    256'h9766C78C_A3094A51_E689AF5F_C6FECD71_89CB6D9B_AEA7F316_2E7B0127_72B8895F,
    256'h3B9C4AA7_A87426FE_7FCE4B63_0F32CD40_80B47849_A3ED7A03_5984FB02_41E6E6A6,
    256'hA976D97A_65543805_391E68C5_6696B587_4C6D1449_625CE208_55CAB846_A439D311,
    256'h4356CA14_3CC2E176_7559CF75_2D6B558A_F071556E_2033EAE3_BA2F7017_1E7821A7,
    256'h06DD38A3_E5F0CF81_2C20E5C5_274E163A_56C459A8_ECD68EB1_D212EA09_0C358245,
    256'h8719F648_8E144463_4A6D820E_F00CD364_20B6527C_0518464E_F08BE557_B4FC002D,
    256'h92CA2696_6C4A6E9F_55EA6C7C_76C4E071_B9E5AA00_11A4E663_1485B408_165CB6B0,
    256'hFD8B05FB_5E8C4311_B9928873_5FBA81DF_B1D6E859_653A83D6_847EB899_916D867C,
    256'h1A710122_69ADA5DC_2618ECC1_310DBB40_E498AA21_D1FA9E39_1DDE72B4_3B6DEC33,
    256'h74D588E2_DA289F45_1211F1C4_57EF6109_7BA60829_440A4EA5_460B0ABE_867B2AB3,
    256'h2865B67A_180C10A9_78A0514C_8BD49290_4DA7457F_A42B9901_724B41D3_420A2323,
    256'hC328A63A_14251E34_759BA7E8_EEA14F22_89C7394E_307E9617_29194836_ABE632C2,
    256'hFFBCA27A_4EA4676B_C4C2D605_59154B01_6D47A692_862297D4_9D80C6D9_6B063D14,
    256'h928324BA_604F1C6A_1E4CC332_F03CB193_9765A213_C1904E3F_524442B9_74AD9296,
    256'hE6E96B8D_C2DED49A_EEB53428_A51BB1B6_DE5BE7D8_C9D86BE7_EA866A80_4A47A404,
    256'h988ED4BA_E00B111C_3588A0AC_BC267144_F038AE42_925639E0_6809EBE6_34DBB210,
    256'h65AA6718_2283DA6F_032EF59A_58968AC1_FDF41CA0_6738C7AC_5151D1DA_1213C86C,
    256'h418C4F90_A9E26549_0A48EC4B_1F751205_AD2B07E0_37A8EC0B_C570724F_8AB2C546,
    256'h65042E1D_4941710D_A3138E95_3891C647_505B001B_C4B53D4C_A3CC0BB1_7EB4C9B4,
    256'hA9E65D8C_6334584C_894C5E00_B7EAA8E1_3492DDD9_98065B14_A47A760B_EE4845EA,
    256'h400D97A1_517D6FD1_55A8A2DF_988A9D01_E2170ECF_8DCE73D4_2229E974_3DC2B718,
    256'h55C59C49_0B5185F1_C4101505_C0A38C15_19376C69_C849162C_6336CE19_2246B732,
    256'h7250C71B_F1A0C4B0_646AD0C5_0B68D95A_2E5086F4_C224C0F2_59640F98_33388106,
    256'hE8121449_579181EC_5774135A_B4A82F64_D56E4492_ACEAC899_06078837_07791F68,
    256'h395954DE_EAEE7A26_1B40E92B_5E5F2218_D71961F7_213F40C3_80AF1890_F04134BB,
    256'h95DD494C_8897EB7C_38F46C21_36A81AB2_4BF4EE30_0C936920_DFA0E73C_228D9DE0,
    256'hC8A71C11_CB8470A9_40895B94_FF042D20_D1759E42_16F93D6A_C9E08D89_5E0EB45C,
    256'hBEAB9688_5DCF1B11_D542F919_B1620DA5_4425C7F4_294801EA_54CC009D_72CF05A8,
    256'h85AAAF0B_A109793E_9A6D88D1_90094164_C8A85E37_80B93A0F_2AD040B6_46501388,
    256'h412F1F55_88258A99_66080856_7570CBE0_117F9D22_3D61360D_13127018_A35A008B
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'hA3C7206C_896AA288_7D8771BD_CB96DA5F_433166B8
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h1E9C6A27_37C3EB9E_00204F0D_D94D0C28,
    256'hF175B268_2B610964_BBE73F8D_9546BDB0_51ED29DE_857CBD5A_888E0B74_ED68BC1D
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h9C2B2E5C_E6567E44_E86FC9FA_5B79F609_0B08F77C_203B16AE_27047899_FA42C837
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h4B993B2B_D311B6C3_2BBCF17B_B4CB2D5A
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hA453CD7A_BDF5BA4E
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hBAEBBE70_437DA6BF
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h590D1BFD_3F0F5CB5_3EAFADCE_1312B592,
    256'h5148C83B_BDD9C18C_EF34828C_1567A267_9D62F029_B62AA06B_8449B307_D93611F9
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h2EB63E41_CAAAC249_9BB16828_7B6199FC_AFE7A448
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hD6349A22_66C33522_317DB491_0816E9F3_5A99F403_273CDFF3_AD3389C1_708A2A7A
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h22B6F355_A2CB8F24_F7E8BB0A_0439B0CD_362939BB_2E0D30A4_9D0522E9_A5B96197
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hAEAC01E3_203BEB21_B48E13B1_27FA42A1_4CEB82B6_610A5457_BBF1CAF5_07098F70
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hDB8EC31E_0C00998F_E5D2429B_122499F3_98D73409_C6CE2E8C_4CC7AB13_C648D6F3
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h8FF69923_25552FD1_10DE6F18_5A80F3AE_276DB241_6FC002D0_4B77C626_E56477E3
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h716EB94C_28F49681_9267FC87_61BE9C1A_B36495FD_7C0CB3AB_FF6A4FC7_F10263B0
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hAE6862F2_F5D3781C_DC459FE1_C6AC6343_A98F8F32_E989297C_02610693_700D68B4
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h72492F96_3EAC9951_5E95F75B_2F747AB4_FD7B6483_4768D0B0_CD8A5828_BBF2CD4B
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h85EEB801_011D8AD4_C0195D90_AE1582AD_51E12EB5_25C2E74D_E16A9346_81A42F3C
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h8FC01CBC_67C9EA62_ADD8EF45_0563C451_44EDF3C3_312B7EB8_8E6B5C61_4553E6A2
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h11B0D83A_2CE3940F_256B3DB0_EB494EE8_937D08C0_8C974099_F25B8179_0BAF3122
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h2141384F_AFBF21AB_369D0ABF_6E68B959,
    256'h301E3403_F5347613_C1C980F2_B67A2495_92B3504A_EEA24843_9F4703D6_03124E32
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h52ADD7D7_4665FCD3_E7FF977D_D899341F,
    256'h621A0FA7_4E5C2CE9_EF80BCCE_0D147EE3_FFA4CB6F_1BE8EECE_2EA06860_734991CF
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h3F1EB798_2AC2C0C2_054167D7_4E4D1EDD
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h21AD35EF_E85D23C8_84C5845D_25CF9AE4
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h741D5E1B
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h6E0131BB_7C1648B6_16C8F6BE_F542F2A7_627AA4C1
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h0979E60D_582E0392
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h0222273A_89B8E0EE_991F6B23_FC6261D9
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h46CAAFEF
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hE02A2CA1_9A88CC49_3B7682DA_9287E7C2_BDD9DDF4
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hFA23DA15_E7D42E08_E9AC008C_70E0B630
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hBF098F0F_567F6710
  };

endpackage : top_earlgrey_rnd_cnst_pkg
