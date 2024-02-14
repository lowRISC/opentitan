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
    40'hE1_8549CB1E
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h9D55_98245508_04312249_A00D9648_1F4176CE_4531A374_C84A7821_CB9993DC
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h44C3BCDF_8087B7FA_CD65E965_4CD85BC6_6D10208C_4FB51B97_BBF4D12C_378CCFD6
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hA5A5BF30_32DB51FA_1EB92F6C_E10E90F9
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hC5C06F73_3DC911A3_21DD4C0A_C2406D46
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h7215DAB3_F2B54A52_E6728678_AF071806
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h8E344D2E_AE4D73C8_FA54DE8A_A4A4F258
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hF3B2A145_FD1950AE_55D693E5_7968117E
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h66DC6341_55E0F815_0242862E_B20EEA9A_1F754471_6551512A_112DED67_8CE824A0,
    256'h8E29C772_795A358E_C30F1BED_D1AF0EC9_D9A9CF36_A2B130D3_2AFE121A_F734F628,
    256'h363AAA0E_93D45C42_3690ED05_BD1E710F_22D10958_89FBD8A7_B57FB1E1_1DF367C1,
    256'hC1EDE3F3_5CFC8F6E_72ABDD73_A9EEFBF8_B7081EB9_F636E13C_A9D21F1E_DEBE60A2
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h2DB6D398
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hFF4E1AEC_AC5CB0F2_239612AF_14F8C0CC_26D70E9A
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hE4612980_D48E6C64_93A50EED_BAC6A46B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h7A8A9B2C_7AEC92F3_9E49478C_398C91DB
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h1841831B
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hF7E60AE6_D8ECA26B_F09ADA50_579C4E63_42AA4163
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h76A61E11_2578BF9F_469FC482_FA14A8F2
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hB75C265C_9CB3B2F1_C44A7287_AB4C0618
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h822E92A0_84A048FF_E9FB8614_0A79D380_55B24B5F_3B3EA79B_D7F203D5_5EABF9F7,
    256'h33D9B0CC_2CA2B394_F2526E44_30C2AFB4_F5B43B16_67039C63_05BF983A_F472A23D
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hB96BE84F
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h699D74AA_B26079D1_1564D8E1_19F807B2_3FAC51F9
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h05BB696B_E7A52B9A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hD3A648F1_D3034BE5_4EAD70B0_CC7BE7D4,
    256'h6DBF2E57_80469B23_26435889_4DED85F4_E6105A1A_AA0E71B8_F581F5B4_3B732E0A
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h33ABE47A_E86D7434_1505C68D_478F07D5,
    256'h208AC532_178D8DF3_02727EA0_BCA9504D_0F16B8B6_3B09595B_981F1A6F_FBF6CA9B
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h0E33FD2C,
    256'h07986C2A_511755F0_72EE7A8E_2FC45E11_1DF07FA0_67F64056_D9BF30D4_8543BEC2
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h31722774_6D588692_343A5D20_839A9569_306E3757_16411E61_447A2642_2452080E,
    256'h898E637C_497F607D_2E0A390D_2D4F2932_9E82066A_3F4C8A02_679F4814_6C179409,
    256'h4010224A_872C3347_2A0C7396_7E1C009B_8C811B0F_3518035B_3C151F71_563E9966,
    256'h7B802819_8D786F1A_1D777679_538B4E68_65114623_45438850_3B07973D_389C596B,
    256'h4D0B8491_4B628F70_2B21015C_2F510413_125A8590_98935F54_55645E9D_05253675
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h20F89CAA,
    256'h47E5CED5_D29CC9CD_B468773E_BACEC14D_A34C505A_EDC70EA1_84C7A341_93D59C73,
    256'h5B5B4E2C_BEE5AB93_CB024D6F_8C0C7001_10CBF014_25DAF514_1DF19A88_2A71D66B,
    256'h5953DBC6_03379DA9_EFB2069B_D79815B2_F8D99A40_E7FDC4FB_13143D77_53CE1CF9
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hA412388E_B94BEA6C,
    256'h303F6E98_BA947313_195941C7_27AA77AD_82BB6A33_0D7158F0_A34905BA_DD82FD2D,
    256'h794A0B20_991F57B4_65F070A7_E305873D_48C16666_0C65C1DE_8E5BC476_4EBB179B,
    256'h97441E8D_C72A0838_538ED55A_E6632F48_60AEB5CF_9ACC14A7_17D0C94D_9C4DC3A6,
    256'h134B2DC8_F0AB3FD4_55DA2909_51A23509_5DEEC52D_2B770FE6_A0D3149D_32CC3A71,
    256'h8A276506_A5E1D49F_100A2999_448832C5_51259721_302C6961_40087668_27A29E81,
    256'hF1D05795_556135AD_568872AD_7267F0AD_F470DF19_86438306_9C731B73_DAB90A7D,
    256'h9A28DA2C_4E3180F8_99DB69A8_38BE0189_6791FD0E_A5522996_737B41A3_DF0B845A,
    256'hF20064BD_AC0605D5_B1CBA801_921B2E71_02782F40_A83B0630_90D2B705_147085AC,
    256'hC5246851_E4989E97_85D02D65_9B0678E1_342C90A9_7A6B0152_7CC4B685_7048B1BF,
    256'h246990CA_0CED2749_CC12EB75_28204C5E_2058956F_0097B868_97C92272_B15D641B,
    256'h87070345_F888D7B7_C44046A8_C00EE060_9B89E031_9F141588_372DCD47_F049757C,
    256'h3B1155F8_F1C4EF91_0C06032F_F3CD4058_0A32E6CA_9C88B0F8_A1B65B41_F8D119A0,
    256'h93263832_19BB8E4F_92CDDA92_5E50C813_32F27827_72F8B546_2758CA5B_1AAAE75A,
    256'h3D675F9A_D957268D_A4A1251E_9AA9EE34_3DAA10D0_76215BB1_B6B26D9D_45720862,
    256'h4DB4813A_B0D6C6C8_E44DD339_58EF884F_27980E00_460000AF_BECA7B60_E29B5020,
    256'hC2CE4406_186E8F4E_4137F1BF_B91A04D2_0235A304_6E899619_07D8C06B_64747404,
    256'h7866A8B7_15BE9C88_5D649D05_D6954F41_31D47111_92408601_6A074B73_A048C664,
    256'hC2B0E00B_EE059C65_589CA0DE_104D9A90_91DFC46A_02D07054_29A448A6_219A31C4,
    256'hFB7B20A0_722CA06D_E38EC196_5A113703_10635672_40BD62A4_AAD38E61_E79E9829,
    256'h214B42FD_716E213E_53362E84_30D5AAD6_9BAAC6B3_C8A12A44_140E7A7A_31B46072,
    256'hDA916202_E51DFD8B_A282EE60_1AD249BC_AA23C750_2D3F6C57_07027C69_E362C0FC,
    256'h4055DC7E_AF16094B_BD99188F_03EACB9C_0BC0E58E_8F81F7DC_297EB09B_74A5880E,
    256'h6619796C_EF8C3CDE_84AE9790_7BAB2842_406FAE8F_D5B5089A_F17B359F_4E1D7A30,
    256'h2125A87B_32D6AF56_E9A4DF7E_DF586942_0D5488E9_29B96D48_2C034F04_631D4481,
    256'h5BE42994_24C1942D_4C351AE9_D93B2CAB_8008A883_C972A489_A5AD549A_805989D5,
    256'hFCF814DB_56346E04_1F20F507_BC50FC4A_BF89263C_595A5443_63665417_13E09983,
    256'hA4E6C7E1_16506454_79916905_4C364E01_63F93718_87D658AE_F0525DE7_A53057DB,
    256'h799DDD1D_1CE8EDF3_44C07C78_5AAF845A_A4CF0895_BC383B06_DB868A86_5CE5716D,
    256'h842E2B0A_5262A6C4_29683C20_985BFB01_AF1C476A_4ABCD145_64637BCE_B8102C85,
    256'hAEE7AAC4_63DBD336_9D9B92E7_FA55A492_1551FFAD_13D70652_3D1E31E2_3323A19A,
    256'h8AC5A7D8_A40EC254_E06B6C17_BDD3208E_88518CE6_60EAAAA0_D855525C_91739648
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'hDDD8EAFF_D1CF7898_08D653C8_5A60ED5C_A7A18028
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h73A93266_A6B6E1FB_1DCE0B54_C02F3E00,
    256'h63EB8BD5_858F5418_A040791C_3C694CD4_8C9CA20B_DE5EEF7A_6BA157FD_0939B457
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hA8F072E7_7EE4859B_243F92CE_B098BE6E_65C35948_0858C396_11E658C9_7FB8D3E9
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hCC0E7F8F_A8725200_C726C8F9_0EF5E2B7
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h4BEEE27C_FA19EA57
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h6CA8A822_5C8E1705
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hB931FB3B_12EFADCD_AA1008BC_15948906,
    256'h6F5D9C83_21E10C03_E5E61B0A_893E95FD_0654DDFF_CACE97A5_4CD668A8_358ED44F
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hB87FDDE5_8A44756A_1C05F720_93384394_C8D7AF15
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h20BDAF59_FE2AE209_B8325D2C_8C35FC96_0679B106_A87E59E6_AEB1B530_2D334010
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h70251696_FBB4BA16_9A6CD82F_AD46A0A5_C04009BB_934C7EF7_B83B6E40_610B4309
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hFCB9DC54_D4276137_F9901D09_A76AEAA1_9DE5C579_FD38BDF3_8F0C21D6_A52226B6
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA4A7BDB0_5FE92161_5BF2FF98_4540F7D4_3ECE76B4_EB133637_74ED2ED4_5545E927
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hF6D9E4AB_AC398D42_C745EEF6_46C1464D_CA86DAFD_7C7C71E6_058DDFD8_71C51CAC
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hBAF4410F_06DCC036_FCD16FCD_E97D1718_91105DD8_95E3A1D0_A19A16D6_DBD8B20F
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hC9E662E1_E1B4982B_3E8EFF63_890DBEAE_926FD468_A77EFDE3_DE5B4CAF_4776A247
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hBABA4C99_08ED16BC_5415EC16_D28C5355_1312FCED_CF2832A6_6CEACF8E_D4D5B616
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h177DD43B_56FA754E_1F53AD65_8193B563_D9BDC6D2_AEE84852_F0CC7371_ED3A6FAA
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h516C144B_34C96DFA_BB6F6E79_208A74F3_5C79F397_C4E4C7E2_2B758184_8A90A125
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h4B2276BE_C9FC1A7A_5722A9AA_CA4DB84A_32E5C698_5A1A6435_118B5F5F_3FD3B931
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h3116B671_92D856DD_742D40E0_72E417AD,
    256'h9A5F2612_04CBCC69_A2147819_B290A4BB_0264347C_0F91B0CE_C93C0129_D85B9580
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h1DBE03F1_7E69DC26_0A79998E_FF5C710B,
    256'h67838ADF_B99A5ECA_671672CF_19BCA6AD_C1EBFAB6_11F19E72_62E0A491_970E51B2
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h8E7026D0_E5DCE9E2_65A416A8_12231CFA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h76E3D982_F8FDCEC9_AE1AF0B8_CD9E1760
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h6EC98106
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h85097395_A09DABEE_6DDD67D1_948B1A89_9435BE41
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hFEE457DE_E82B6E06
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h663C2917_39FF0E7D_644758FE_E1C58564
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hCF346D96
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hAE357A7A_3B2CD206_3D7F3AB3_043AC11B_7B211B84
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hC652D737_2432FCC4_D3092BD6_383FDBA3
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h5279FCBC_D2BD2C13
  };

endpackage : top_earlgrey_rnd_cnst_pkg
